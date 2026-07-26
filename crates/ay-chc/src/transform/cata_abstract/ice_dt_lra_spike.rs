// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SPIKE harness (make-or-break gate) for the Horn-ICE decision-tree learner on
//! RAW LRA transition systems (task #27, LRA-Lin functional gap).
//!
//! The DT learner ([`super::ice_dt`]) synthesizes DISJUNCTIVE invariants and was
//! proven on cata-abstracted ADT-LIA (sortedness). This harness answers the
//! make-or-break question for the LRA-Lin campaign gap: can the DT-learner CORE
//! synthesize an inductive, query-excluding invariant for a small LRA-Lin SAFE
//! transition system, given a generic Real/Bool atom set?
//!
//! Method: SPIKE-FIRST + RE-SUBSTITUTION. Each test builds a tiny single-pred
//! Real (or Real+Bool) transition system directly as a [`ChcProblem`] (fact =
//! init, transition rule, query), runs [`super::ice_dt::solve_lra_ice_dt`] with
//! a generic atom set, and PROVES the result by re-substitution: the learned
//! invariant `I` must satisfy `init ⊆ I`, `I ∧ trans ⊆ I'`, `I ∧ query ⊆ false`
//! — checked on the ORIGINAL clauses by AY's own SMT via
//! [`crate::engines::validate_external_invariant_model`] (the SAME fail-closed
//! gate every Safe verdict uses). These tests are self-contained (no corpus).

use std::time::Duration;

use ay_core::time::Instant;

use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, InvariantModel,
    PdrConfig, PredicateId,
};

/// Real literal `c/1`.
fn real(c: i64) -> ChcExpr {
    ChcExpr::Real(c, 1)
}

/// Re-substitution proof on the ORIGINAL clauses (init ⊆ I, I∧trans ⊆ I',
/// I∧query ⊆ false) via AY's fail-closed per-rule verifier.
fn recert(problem: &ChcProblem, model: &InvariantModel) -> bool {
    let cfg = PdrConfig {
        strict_proofs: true,
        solve_timeout: Some(Duration::from_secs(15)),
        ..PdrConfig::default()
    };
    matches!(
        crate::engines::validate_external_invariant_model(problem, model, &cfg),
        Ok(true)
    )
}

/// Pretty-print the learned invariant for one predicate.
fn dump_model(problem: &ChcProblem, model: &InvariantModel) -> String {
    let mut out = String::new();
    for pred in problem.predicates() {
        if let Some(interp) = model.get(&pred.id) {
            let sig: Vec<String> = interp
                .vars
                .iter()
                .map(|v| format!("{} {}", v.name, v.sort))
                .collect();
            out.push_str(&format!(
                "  {}({}) := {}\n",
                pred.name,
                sig.join(", "),
                InvariantModel::expr_to_smtlib(&interp.formula)
            ));
        }
    }
    out
}

// ───────────────────────────────────────────────────────────────────────────
// (A) CONJUNCTIVE baseline: monotone Real counter. Proves the DT core drives
//     LRA queries at all (init/trans/query all decidable, invariant is x ≥ 0).
// ───────────────────────────────────────────────────────────────────────────

/// `P(x:Real)`, init `x=0`, trans `x' = x+1`, query `x < 0`. SAFE.
/// Inductive invariant: `x ≥ 0`.
fn monotone_counter() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Real]);
    let x = ChcVar::new("x", ChcSort::Real);
    let xp = ChcVar::new("xp", ChcSort::Real);
    let vx = || ChcExpr::var(x.clone());
    let vxp = || ChcExpr::var(xp.clone());

    // init: x = 0 ⇒ P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(vx(), real(0))),
        ClauseHead::Predicate(p, vec![vx()]),
    ));
    // trans: P(x) ∧ x' = x + 1 ⇒ P(x')
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![vx()])],
            Some(ChcExpr::eq(vxp(), ChcExpr::add(vx(), real(1)))),
        ),
        ClauseHead::Predicate(p, vec![vxp()]),
    ));
    // query: P(x) ∧ x < 0 ⇒ false
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![vx()])], Some(ChcExpr::lt(vx(), real(0)))),
        ClauseHead::False,
    ));
    (problem, p)
}

#[test]
fn lra_ice_dt_monotone_counter() {
    let (problem, _p) = monotone_counter();
    let start = Instant::now();
    let model =
        super::ice_dt::solve_lra_ice_dt(&problem, &[-1, 0, 1], start + Duration::from_secs(20));
    let wall = start.elapsed();
    match &model {
        Some(m) => {
            eprintln!(
                "[monotone_counter] DT solved in {wall:?}:\n{}",
                dump_model(&problem, m)
            );
            assert!(
                recert(&problem, m),
                "[monotone_counter] learned invariant must re-certify on ORIGINAL clauses"
            );
            eprintln!("[monotone_counter] RE-SUBSTITUTION PASS");
        }
        None => panic!("[monotone_counter] DT core returned None (wall={wall:?}) — LRA SPIKE FAIL"),
    }
}

// ───────────────────────────────────────────────────────────────────────────
// (B) DISJUNCTIVE Real+Bool: mode-toggling sign-flipper. This is the crux —
//     it mirrors s3_srvr_4's structure (a Boolean-rooted invariant over reals)
//     and REQUIRES a genuine disjunction (no single conjunction of atoms works).
// ───────────────────────────────────────────────────────────────────────────

/// `P(b:Bool, x:Real)`, init `b ∧ x=1`, trans `b' = ¬b ∧ x' = -x`,
/// query `x = 0`. SAFE. The reachable set is exactly `{(true,1),(false,-1)}`;
/// the strongest expressible invariant is the DISJUNCTION
/// `(b ∧ x ≥ 1) ∨ (¬b ∧ x ≤ -1)`, which excludes `x = 0`.
fn sign_flipper() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Bool, ChcSort::Real]);
    let b = ChcVar::new("b", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Real);
    let bp = ChcVar::new("bp", ChcSort::Bool);
    let xp = ChcVar::new("xp", ChcSort::Real);
    let vb = || ChcExpr::var(b.clone());
    let vx = || ChcExpr::var(x.clone());
    let vbp = || ChcExpr::var(bp.clone());
    let vxp = || ChcExpr::var(xp.clone());

    // init: b ∧ x = 1 ⇒ P(b, x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(vb(), ChcExpr::eq(vx(), real(1)))),
        ClauseHead::Predicate(p, vec![vb(), vx()]),
    ));
    // trans: P(b,x) ∧ b' = ¬b ∧ x' = -x ⇒ P(b', x')
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![vb(), vx()])],
            Some(ChcExpr::and(
                ChcExpr::eq(vbp(), ChcExpr::not(vb())),
                ChcExpr::eq(vxp(), ChcExpr::neg(vx())),
            )),
        ),
        ClauseHead::Predicate(p, vec![vbp(), vxp()]),
    ));
    // query: P(b,x) ∧ x = 0 ⇒ false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![vb(), vx()])],
            Some(ChcExpr::eq(vx(), real(0))),
        ),
        ClauseHead::False,
    ));
    (problem, p)
}

#[test]
fn lra_ice_dt_disjunctive_sign_flipper() {
    let (problem, _p) = sign_flipper();
    let start = Instant::now();
    let model =
        super::ice_dt::solve_lra_ice_dt(&problem, &[-1, 0, 1], start + Duration::from_secs(20));
    let wall = start.elapsed();
    match &model {
        Some(m) => {
            eprintln!(
                "[sign_flipper] DT solved (DISJUNCTIVE) in {wall:?}:\n{}",
                dump_model(&problem, m)
            );
            assert!(
                recert(&problem, m),
                "[sign_flipper] learned DISJUNCTIVE invariant must re-certify on ORIGINAL clauses"
            );
            eprintln!("[sign_flipper] RE-SUBSTITUTION PASS (disjunctive LRA+Bool)");
        }
        None => panic!(
            "[sign_flipper] DT core returned None (wall={wall:?}) — DISJUNCTIVE LRA SPIKE FAIL"
        ),
    }
}

// ───────────────────────────────────────────────────────────────────────────
// (C) ADVERSARIAL no-false-Safe: an UNSAFE Real system. The DT learner must
//     NEVER return a re-certifying model (soundness: a wrong tree → None or a
//     candidate that fails the re-cert gate, never a false Safe).
// ───────────────────────────────────────────────────────────────────────────

/// `P(x:Real)`, init `x=0`, trans `x' = x-1` (decrement), query `x < 0`.
/// UNSAFE — `x` reaches `-1` from the fact, so the error IS reachable.
fn unsafe_decrementer() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Real]);
    let x = ChcVar::new("x", ChcSort::Real);
    let xp = ChcVar::new("xp", ChcSort::Real);
    let vx = || ChcExpr::var(x.clone());
    let vxp = || ChcExpr::var(xp.clone());

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(vx(), real(0))),
        ClauseHead::Predicate(p, vec![vx()]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![vx()])],
            Some(ChcExpr::eq(vxp(), ChcExpr::sub(vx(), real(1)))),
        ),
        ClauseHead::Predicate(p, vec![vxp()]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![vx()])], Some(ChcExpr::lt(vx(), real(0)))),
        ClauseHead::False,
    ));
    (problem, p)
}

#[test]
fn lra_ice_dt_never_false_safe_on_unsafe() {
    let (problem, _p) = unsafe_decrementer();
    let outcome = super::ice_dt::solve_lra_ice_dt(
        &problem,
        &[-1, 0, 1],
        Instant::now() + Duration::from_secs(20),
    );
    if let Some(model) = outcome {
        assert!(
            !recert(&problem, &model),
            "[unsafe_decrementer] DT learner produced a FALSE Safe on a genuinely UNSAFE system"
        );
        eprintln!("[unsafe_decrementer] produced a candidate but it correctly FAILED re-cert");
    } else {
        eprintln!("[unsafe_decrementer] DT core returned None (correct: no invariant exists)");
    }
}

// ───────────────────────────────────────────────────────────────────────────
// (D) SCALE-shape pin for the diagnosed s3_srvr_4 family. The ordinary test
//     stays deterministic and built-in; external Real-TS campaigns run through
//     the bounded corpus example.
// ───────────────────────────────────────────────────────────────────────────

/// Build a bounded atom set for a raw single-pred TS: all Bool columns as 0/1
/// atoms, plus (optionally) `real_k` leading Real columns covered by `≥0`,
/// `≤0`, `≥1`, `≤1` interval atoms. Over the predicate's canonical arg vars.
fn bounded_ts_atoms(pid: PredicateId, arg_sorts: &[ChcSort], real_k: usize) -> Vec<ChcExpr> {
    use super::disj_abstract::canonical_var;
    let mut pool: Vec<ChcExpr> = Vec::new();
    // Bool columns.
    for (i, s) in arg_sorts.iter().enumerate() {
        if matches!(s, ChcSort::Bool) {
            pool.push(ChcExpr::var(canonical_var(pid, i, s)));
        }
    }
    // Leading Real columns.
    let mut covered = 0usize;
    for (i, s) in arg_sorts.iter().enumerate() {
        if covered >= real_k {
            break;
        }
        if matches!(s, ChcSort::Real) {
            let v = || ChcExpr::var(canonical_var(pid, i, s));
            pool.push(ChcExpr::ge(v(), real(0)));
            pool.push(ChcExpr::le(v(), real(0)));
            pool.push(ChcExpr::ge(v(), real(1)));
            pool.push(ChcExpr::le(v(), real(1)));
            covered += 1;
        }
    }
    pool
}

#[test]
fn lra_ice_dt_s3_srvr_4_scale() {
    let (builtin, _) = monotone_counter();
    let builtin_atoms: Vec<Vec<ChcExpr>> = builtin
        .predicates()
        .iter()
        .map(|p| bounded_ts_atoms(p.id, &p.arg_sorts, 1))
        .collect();
    assert!(
        builtin_atoms.iter().all(|atoms| !atoms.is_empty()),
        "bounded Real columns must produce a finite atom set"
    );
    let builtin_model = super::ice_dt::run_ice_dt_core(
        &builtin,
        builtin_atoms,
        Instant::now() + Duration::from_secs(10),
    )
    .expect("bounded-atom DT core must solve the built-in Real counter");
    assert!(
        recert(&builtin, &builtin_model),
        "bounded-atom model must re-certify on the original built-in clauses"
    );
}

// ───────────────────────────────────────────────────────────────────────────
// (E) BODY-ATOM HARVEST spike: the STEP-1 atom-inadequacy fix. The bool-only
//     abstraction reaches the query in the closure because the Real program-
//     counter guard that actually blocks the bad Boolean combo is invisible.
//     Harvest the current-state comparison atoms straight out of the clause
//     bodies (the guard literals) and hand them to the DT core.
// ───────────────────────────────────────────────────────────────────────────

/// Collect every comparison sub-expression (Eq/Ne/Lt/Le/Gt/Ge over two terms)
/// reachable in `e`, without descending into a comparison's term children.
fn collect_comparisons(e: &ChcExpr, out: &mut Vec<ChcExpr>) {
    use crate::ChcOp;
    if let ChcExpr::Op(op, args) = e {
        if matches!(
            op,
            ChcOp::Eq | ChcOp::Ne | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge
        ) && args.len() == 2
        {
            out.push(e.clone());
            return;
        }
        for a in args {
            collect_comparisons(a, out);
        }
    }
}

/// Harvest, per predicate, the atom set = (Bool columns as 0/1 atoms) ∪
/// (current-state comparison guards from clause bodies, rewritten over the
/// predicate's canonical arg vars). A comparison qualifies only when EVERY one
/// of its variables is an argument variable of the SAME body predicate
/// application (i.e. a pure current-state literal), so next-state / intermediate
/// guards are naturally excluded.
fn harvest_body_atoms(problem: &ChcProblem) -> Vec<Vec<ChcExpr>> {
    use super::disj_abstract::canonical_var;
    use std::collections::HashMap;
    let preds = problem.predicates();
    let mut pools: Vec<Vec<ChcExpr>> = vec![Vec::new(); preds.len()];
    let push = |pool: &mut Vec<ChcExpr>, e: ChcExpr| {
        if !pool.iter().any(|p| *p == e) {
            pool.push(e);
        }
    };
    // (1) Bool columns as atoms.
    for (pi, pred) in preds.iter().enumerate() {
        for (i, s) in pred.arg_sorts.iter().enumerate() {
            if matches!(s, ChcSort::Bool) {
                push(&mut pools[pi], ChcExpr::var(canonical_var(pred.id, i, s)));
            }
        }
    }
    // (2) Current-state comparison guards from every clause body.
    for clause in problem.clauses() {
        let Some(constraint) = &clause.body.constraint else {
            continue;
        };
        let mut var_col: HashMap<String, (usize, usize)> = HashMap::new();
        for (bpid, bargs) in &clause.body.predicates {
            for (col, arg) in bargs.iter().enumerate() {
                if let ChcExpr::Var(v) = arg {
                    var_col.insert(v.name.clone(), (bpid.index(), col));
                }
            }
        }
        if var_col.is_empty() {
            continue;
        }
        let mut cmps = Vec::new();
        collect_comparisons(constraint, &mut cmps);
        for cmp in cmps {
            let vars = cmp.vars();
            if vars.is_empty() {
                continue;
            }
            let mut pid_opt: Option<usize> = None;
            let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
            let mut ok = true;
            for v in &vars {
                match var_col.get(&v.name) {
                    Some(&(pi, col)) => {
                        if let Some(prev) = pid_opt {
                            if prev != pi {
                                ok = false;
                                break;
                            }
                        }
                        pid_opt = Some(pi);
                        let sort = &preds[pi].arg_sorts[col];
                        subst.push((
                            v.clone(),
                            ChcExpr::var(canonical_var(preds[pi].id, col, sort)),
                        ));
                    }
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let pi = pid_opt.expect("non-empty vars ⇒ pid set");
            push(&mut pools[pi], cmp.substitute(&subst));
        }
    }
    pools
}

#[test]
fn lra_ice_dt_s3_srvr_4_bodyatoms() {
    let (builtin, _) = monotone_counter();
    let builtin_atoms = harvest_body_atoms(&builtin);
    assert!(
        builtin_atoms.iter().all(|atoms| !atoms.is_empty()),
        "the built-in query guard must be harvested as a current-state atom"
    );
    let builtin_model = super::ice_dt::run_ice_dt_core(
        &builtin,
        builtin_atoms,
        Instant::now() + Duration::from_secs(10),
    )
    .expect("body-harvested DT core must solve the built-in Real counter");
    assert!(
        recert(&builtin, &builtin_model),
        "body-harvested model must re-certify on the original built-in clauses"
    );
}
