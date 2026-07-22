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
use ay_test_support::env::{lock_env, ScopedEnvVar};

use crate::{
    ChcExpr, ChcParser, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
    InvariantModel, PdrConfig, PredicateId,
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
// (D) SCALE experiment: the diagnosed case s3_srvr_4 (46-var single-pred Real
//     TS, Boolean-rooted bad state). `#[ignore]`: reads a real benchmark whose
//     absolute path is in `AY_LRA_TS`. Configurable atom set via `AY_LRA_BOOL_
//     ONLY` (default 1: 3 Bool atoms only) and `AY_LRA_REAL_K` (# of leading
//     Real columns to also cover with {0,1} bound atoms, default 0).
//
//     Run: AY_LRA_TS=<abs path> cargo test -p ay-chc --lib lra_ice_dt_s3_srvr
//          -- --ignored --nocapture --test-threads=1
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
#[ignore = "manual scale experiment; requires an external benchmark in AY_LRA_TS"]
fn lra_ice_dt_s3_srvr_4_scale() {
    let path = match std::env::var("AY_LRA_TS") {
        Ok(p) => p,
        Err(_) => {
            eprintln!("SKIP: set AY_LRA_TS to the absolute path of a single-pred Real .smt2 TS");
            return;
        }
    };
    let bool_only = std::env::var("AY_LRA_BOOL_ONLY")
        .map(|v| v != "0")
        .unwrap_or(true);
    let real_k = if bool_only {
        0
    } else {
        std::env::var("AY_LRA_REAL_K")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(0)
    };
    let budget = Duration::from_secs(
        std::env::var("AY_LRA_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(90),
    );

    let smt = std::fs::read_to_string(&path).expect("read TS benchmark");
    let problem = ChcParser::parse(&smt).expect("benchmark CHC should parse");
    let preds = problem.predicates();
    eprintln!(
        "\n=== s3_srvr scale: {} preds, {} clauses; atoms: bool_only={} real_k={} budget={:?} ===",
        preds.len(),
        problem.clauses().len(),
        bool_only,
        real_k,
        budget
    );
    for p in preds {
        let n_bool = p
            .arg_sorts
            .iter()
            .filter(|s| matches!(s, ChcSort::Bool))
            .count();
        let n_real = p
            .arg_sorts
            .iter()
            .filter(|s| matches!(s, ChcSort::Real))
            .count();
        eprintln!(
            "  pred {} ({}): {} args ({} Bool, {} Real)",
            p.id.index(),
            p.name,
            p.arg_sorts.len(),
            n_bool,
            n_real
        );
    }

    // ── Direct executor probe: can AY's SMT decide the raw transition
    //    relation at all? This isolates the SMT-core blocker from the learner.
    {
        use crate::smt::PdrExecutorBackend;
        let mut backend = PdrExecutorBackend::new();
        let probe_budget = Duration::from_secs(15);
        for (ci, clause) in problem.clauses().iter().enumerate() {
            let Some(c) = &clause.body.constraint else {
                continue;
            };
            if clause.body.predicates.is_empty() {
                continue; // fact clause — trivial
            }
            let t0 = Instant::now();
            let res = backend.check_sat(c, probe_budget);
            eprintln!(
                "  [probe] clause {ci} raw body-constraint check_sat = {:?} in {:?}",
                res,
                t0.elapsed()
            );
        }
    }

    // Build one atom vec per predicate (index-aligned with predicate order).
    let atoms: Vec<Vec<ChcExpr>> = preds
        .iter()
        .map(|p| bounded_ts_atoms(p.id, &p.arg_sorts, real_k))
        .collect();
    for (p, a) in preds.iter().zip(&atoms) {
        eprintln!("  pred {} -> {} atoms", p.name, a.len());
    }

    let start = Instant::now();
    let model = super::ice_dt::run_ice_dt_core(&problem, atoms, start + budget);
    let wall = start.elapsed();

    match &model {
        Some(m) => {
            eprintln!(
                "[s3_srvr] DT core produced a candidate in {wall:?}:\n{}",
                dump_model(&problem, m)
            );
            let ok = recert(&problem, m);
            eprintln!(
                "[s3_srvr] RE-SUBSTITUTION on ORIGINAL clauses: {}",
                if ok { "PASS" } else { "FAIL" }
            );
            if ok {
                eprintln!("[s3_srvr] *** SCALE WIN: DT invariant re-certifies s3_srvr_4 ***");
            }
        }
        None => {
            eprintln!("[s3_srvr] DT core returned None in {wall:?} (fail-closed: see AY_ICE_DT_TRACE for the exact reason)");
        }
    }
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
#[ignore = "manual body-atom experiment; requires AY_LRA_TS and serial execution"]
fn lra_ice_dt_s3_srvr_4_bodyatoms() {
    let path = match std::env::var("AY_LRA_TS") {
        Ok(p) => p,
        Err(_) => {
            eprintln!("SKIP: set AY_LRA_TS to the absolute path of a single-pred Real .smt2 TS");
            return;
        }
    };
    let budget = Duration::from_secs(
        std::env::var("AY_LRA_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(120),
    );
    let atom_cap: usize = std::env::var("AY_LRA_ATOM_CAP")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(64);
    // The raw-LRA guard harvest legitimately exceeds the cata default (40); let
    // the core admit up to the u64 ceiling for this diagnostic run. Serialized
    // + restore-on-exit via the workspace env choke point; the guard holds for
    // the rest of this diagnostic body.
    let _env_lock = lock_env();
    let _max_atoms = ScopedEnvVar::set("AY_ICE_DT_MAX_ATOMS", &atom_cap.min(64).to_string());
    let smt = std::fs::read_to_string(&path).expect("read TS benchmark");
    let problem = ChcParser::parse(&smt).expect("benchmark CHC should parse");

    let mut atoms = harvest_body_atoms(&problem);

    // Optional column filter: AY_LRA_KEEP_COLS="0,1,2,14" keeps only atoms whose
    // canonical vars all lie in the given column set (plus Bool columns, always).
    // Empty ⇒ keep all. Lets the spike isolate which columns the invariant needs
    // (e.g. bools + the program counter) from unbounded data columns whose guards
    // generate endless non-reachable edges (the closure-stall divergence).
    if let Ok(spec) = std::env::var("AY_LRA_KEEP_COLS") {
        let keep: std::collections::HashSet<usize> = spec
            .split(',')
            .filter_map(|s| s.trim().parse().ok())
            .collect();
        for (pi, pred) in problem.predicates().iter().enumerate() {
            let bool_cols: std::collections::HashSet<usize> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .filter(|(_, s)| matches!(s, ChcSort::Bool))
                .map(|(i, _)| i)
                .collect();
            let pfx = format!("__cxd{}_", pred.id.index());
            atoms[pi].retain(|atom| {
                atom.vars().iter().all(|v| {
                    v.name
                        .strip_prefix(&pfx)
                        .and_then(|s| s.parse::<usize>().ok())
                        .is_some_and(|col| keep.contains(&col) || bool_cols.contains(&col))
                })
            });
        }
    }

    for (p, a) in problem.predicates().iter().zip(&atoms) {
        eprintln!(
            "  pred {} -> {} harvested atoms (cap {})",
            p.name,
            a.len(),
            atom_cap
        );
        for at in a.iter().take(70) {
            eprintln!("      {}", InvariantModel::expr_to_smtlib(at));
        }
    }
    // Trim to cap (keep first `atom_cap` — Bool cols first, then guards in
    // clause order) so the u64 bitmask / MAX_ATOMS_PER_PRED hold.
    for a in &mut atoms {
        if a.len() > atom_cap {
            a.truncate(atom_cap);
        }
    }

    let start = Instant::now();
    let model = super::ice_dt::run_ice_dt_core(&problem, atoms, start + budget);
    let wall = start.elapsed();
    match &model {
        Some(m) => {
            eprintln!(
                "[bodyatoms] DT core produced a candidate in {wall:?}:\n{}",
                dump_model(&problem, m)
            );
            let ok = recert(&problem, m);
            eprintln!(
                "[bodyatoms] RE-SUBSTITUTION on ORIGINAL clauses: {}",
                if ok { "PASS" } else { "FAIL" }
            );
            if ok {
                eprintln!(
                    "[bodyatoms] *** SCALE WIN: body-harvested DT invariant re-certifies ***"
                );
            }
        }
        None => {
            eprintln!(
                "[bodyatoms] DT core returned None in {wall:?} (fail-closed: see AY_ICE_DT_TRACE)"
            );
        }
    }
}
