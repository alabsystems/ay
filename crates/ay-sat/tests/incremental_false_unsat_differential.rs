// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential / oracle fuzzer hunting a suspected *incremental false-UNSAT*
//! bug in ay-sat, as exercised by an external IC3/PDR model checker.
//!
//! ## The suspected bug
//!
//! An IC3/PDR loop drives the raw SAT layer incrementally:
//!   (add clauses at root) then (solve under assumptions), repeated for many
//!   rounds on constraint-dense problems. The suspicion is that after many such
//!   rounds ay-sat returns UNSAT for a query whose accumulated clause set +
//!   assumptions is actually SAT. Incremental *preprocessing* (BVE/subsumption)
//!   is the prime suspect: derived clauses from an early preprocessing pass can
//!   persist and exclude models that later-added clauses make necessary
//!   (cf. the existing #7987 / #8822 regressions).
//!
//! ## Two independent oracles (no trust in the solver under test)
//!
//! 1. **Planted-solution oracle (definitive).** We pick a hidden assignment
//!    `sol` up front and only ever add clauses that `sol` satisfies. Therefore
//!    `sol` is a model of the *entire* accumulated clause DB at every round.
//!    On rounds where the assumptions are also consistent with `sol`, the query
//!    is provably SAT. If the incremental solver returns UNSAT on such a round,
//!    that is a false-UNSAT with an explicit witness — no other solver needed.
//!
//! 2. **Incremental-vs-fresh differential + brute force (adjudication).** On
//!    rounds whose assumptions are adversarial (may legitimately be UNSAT), we
//!    re-solve the exact same accumulated clause set + assumptions with a FRESH
//!    solver instance. Incremental and from-scratch MUST agree. On disagreement
//!    (and for small var counts always available) we brute-force the ground
//!    truth to identify which side is wrong.
//!
//! The IC3-like access pattern is: interleave provably-SAT queries with
//! adversarial (often-UNSAT) queries on a growing, dense clause DB, so that
//! state corruption from an UNSAT query would surface as a false-UNSAT on the
//! next provably-SAT query.
//!
//! Run: `cargo test -p ay-sat --test incremental_false_unsat_differential -- --nocapture`

#![allow(clippy::print_stderr, clippy::print_stdout, clippy::panic)]

use ay_sat::{AssumeResult, Literal, SatUnknownReason, Solver, Variable};
use ntest::timeout;
use std::collections::HashSet;
use std::fmt::Write as _;

// ---------------------------------------------------------------------------
// Deterministic RNG (SplitMix64) — reproducible per seed.
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_add(0x1234_5678_9abc_def0))
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % (n as u64)) as usize
    }
    fn boolean(&mut self) -> bool {
        self.next_u64() & 1 == 0
    }
    /// Returns true with probability `pct`/100.
    fn chance(&mut self, pct: u64) -> bool {
        self.next_u64() % 100 < pct
    }
}

// ---------------------------------------------------------------------------
// Literal helpers.
// ---------------------------------------------------------------------------

fn lit(var: usize, positive: bool) -> Literal {
    let v = Variable::new(var as u32);
    if positive {
        Literal::positive(v)
    } else {
        Literal::negative(v)
    }
}

/// True iff `assign` satisfies at least one literal of `clause`.
fn clause_sat(clause: &[Literal], assign: &[bool]) -> bool {
    clause.iter().any(|l| {
        let v = l.variable().index();
        assign.get(v).copied().unwrap_or(false) == l.is_positive()
    })
}

/// Random clause of length `len` (distinct vars) that is guaranteed satisfied
/// by `sol`. We build a random clause and, if `sol` does not already satisfy
/// it, flip one literal to its sol-satisfying polarity.
fn planted_clause(rng: &mut Rng, num_vars: usize, len: usize, sol: &[bool]) -> Vec<Literal> {
    let mut seen = HashSet::new();
    let mut vars = Vec::with_capacity(len);
    while vars.len() < len {
        let v = rng.below(num_vars);
        if seen.insert(v) {
            vars.push(v);
        }
    }
    let mut clause: Vec<Literal> = vars.iter().map(|&v| lit(v, rng.boolean())).collect();
    if !clause_sat(&clause, sol) {
        // Force satisfaction: pick one var, set its literal to the sol polarity.
        let idx = rng.below(clause.len());
        let v = clause[idx].variable().index();
        clause[idx] = lit(v, sol[v]);
    }
    debug_assert!(clause_sat(&clause, sol));
    clause
}

/// Brute-force: does a satisfying assignment consistent with `assumptions`
/// exist for `db`? Only called for small `num_vars`.
fn brute_force_sat(num_vars: usize, db: &[Vec<Literal>], assumptions: &[Literal]) -> bool {
    assert!(num_vars <= 22, "brute force only for <= 22 vars");
    let total: u64 = 1u64 << num_vars;
    let mut assign = vec![false; num_vars];
    'outer: for mask in 0..total {
        for (i, a) in assign.iter_mut().enumerate() {
            *a = (mask >> i) & 1 == 1;
        }
        for a in assumptions {
            if assign[a.variable().index()] != a.is_positive() {
                continue 'outer;
            }
        }
        for c in db {
            if !clause_sat(c, &assign) {
                continue 'outer;
            }
        }
        return true;
    }
    false
}

/// Best-effort SAT-model check: returns the index of a clause the model
/// definitively violates (all its vars in range, none satisfied), else None.
fn model_violation(db: &[Vec<Literal>], model: &[bool]) -> Option<usize> {
    for (i, c) in db.iter().enumerate() {
        let mut all_in_range = true;
        let mut satisfied = false;
        for l in c {
            let v = l.variable().index();
            if v >= model.len() {
                all_in_range = false;
            } else if model[v] == l.is_positive() {
                satisfied = true;
            }
        }
        if all_in_range && !satisfied {
            return Some(i);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Solver configuration variants.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
enum Config {
    /// Exactly how the real IC3 solver configures ay-sat (preprocessing off,
    /// IC3-tuned learned-clause GC + VSIDS persistence). See
    /// `crates/ay-chc/src/ic3/solver.rs`.
    Ic3Mode,
    /// `set_incremental_mode()` — disables destructive inprocessing but keeps
    /// the ordinary incremental reset path.
    IncrementalMode,
    /// Prime suspect: preprocessing ON with BVE/BCE/subsume/probe/vivify
    /// explicitly enabled, driven incrementally across many add-clause rounds.
    PreprocessHeavy,
}

impl Config {
    fn name(self) -> &'static str {
        match self {
            Config::Ic3Mode => "ic3_mode",
            Config::IncrementalMode => "incremental_mode",
            Config::PreprocessHeavy => "preprocess_heavy(BVE+BCE+subsume+probe+vivify)",
        }
    }
    fn apply(self, s: &mut Solver) {
        match self {
            Config::Ic3Mode => s.set_ic3_mode(),
            Config::IncrementalMode => s.set_incremental_mode(),
            Config::PreprocessHeavy => {
                s.set_preprocess_enabled(true);
                s.set_bve_enabled(true);
                s.set_bce_enabled(true);
                s.set_subsume_enabled(true);
                s.set_probe_enabled(true);
                s.set_vivify_enabled(true);
            }
        }
    }
}

fn assume_verdict(r: AssumeResult) -> Option<bool> {
    match r {
        AssumeResult::Sat(_) => Some(true),
        AssumeResult::Unsat(..) => Some(false),
        AssumeResult::Unknown => None,
        _ => None,
    }
}

/// Fresh from-scratch solve of `db` + `assumptions` with a well-tested
/// single-shot configuration (default preprocessing). Independent reference.
fn fresh_verdict(num_vars: usize, db: &[Vec<Literal>], assumptions: &[Literal]) -> Option<bool> {
    let mut s = Solver::new(num_vars);
    for c in db {
        s.add_clause(c.clone());
    }
    assume_verdict(s.solve_with_assumptions(assumptions).into_inner())
}

// ---------------------------------------------------------------------------
// Reproduction dump.
// ---------------------------------------------------------------------------

fn dump_repro(
    kind: &str,
    config: Config,
    seed: u64,
    round: usize,
    num_vars: usize,
    sol: &[bool],
    db: &[Vec<Literal>],
    assumptions: &[Literal],
) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "\n================ {kind} ================");
    let _ = writeln!(
        out,
        "config={} seed={seed} round={round} num_vars={num_vars} clauses={}",
        config.name(),
        db.len()
    );
    let _ = write!(out, "planted sol (var=val):");
    for (v, b) in sol.iter().enumerate() {
        let _ = write!(out, " {v}={}", u8::from(*b));
    }
    let _ = writeln!(out);
    let _ = write!(out, "assumptions:");
    for a in assumptions {
        let s = if a.is_positive() { "" } else { "-" };
        let _ = write!(out, " {s}{}", a.variable().index());
    }
    let _ = writeln!(out);
    let _ = writeln!(out, "accumulated CNF (DIMACS, vars 1-based):");
    let _ = writeln!(out, "p cnf {num_vars} {}", db.len());
    for c in db {
        for l in c {
            let v = l.variable().index() + 1;
            let _ = write!(out, "{}{v} ", if l.is_positive() { "" } else { "-" });
        }
        let _ = writeln!(out, "0");
    }
    let _ = writeln!(
        out,
        "Re-run: cargo test -p ay-sat --test incremental_false_unsat_differential -- --nocapture"
    );
    out
}

// ---------------------------------------------------------------------------
// Campaign driver.
// ---------------------------------------------------------------------------

#[derive(Default)]
struct CampaignStats {
    guaranteed_sat_rounds: usize,
    adversarial_rounds: usize,
    observed_unsat: usize,
    observed_sat: usize,
    differential_agree: usize,
}

/// Drive one incremental solver instance IC3-style over `rounds` rounds.
/// Panics with a full reproduction on any detected false-UNSAT / disagreement.
#[allow(clippy::too_many_lines)]
fn run_seed(
    config: Config,
    seed: u64,
    num_vars: usize,
    rounds: usize,
    init_clauses: usize,
    add_per_round: usize,
    adversarial_pct: u64,
    stats: &mut CampaignStats,
) {
    let brute_ok = num_vars <= 20;
    let mut rng = Rng::new(seed ^ ((config as u64).wrapping_mul(0x9E37)));

    // Planted hidden solution.
    let sol: Vec<bool> = (0..num_vars).map(|_| rng.boolean()).collect();

    let mut solver = Solver::new(num_vars);
    config.apply(&mut solver);

    let mut db: Vec<Vec<Literal>> = Vec::new();
    let rand_len = |rng: &mut Rng| 2 + rng.below(3); // 2..=4 literals

    // Seed a dense initial clause DB (all planted-satisfiable).
    for _ in 0..init_clauses {
        let l = rand_len(&mut rng);
        let c = planted_clause(&mut rng, num_vars, l, &sol);
        solver.add_clause(c.clone());
        db.push(c);
    }

    for round in 0..rounds {
        // Choose assumptions.
        let adversarial = rng.chance(adversarial_pct);
        let n_assume = rng.below(num_vars / 3 + 1);
        let mut seen = HashSet::new();
        let mut assumptions = Vec::with_capacity(n_assume);
        while assumptions.len() < n_assume {
            let v = rng.below(num_vars);
            if seen.insert(v) {
                // Guaranteed-SAT rounds: assume the sol polarity so `sol`
                // remains a model. Adversarial rounds: random polarity.
                let pol = if adversarial { rng.boolean() } else { sol[v] };
                assumptions.push(lit(v, pol));
            }
        }

        let raw = solver
            .solve_with_assumptions_interruptible(&assumptions, || false)
            .into_inner();
        let incr = assume_verdict(raw.clone());

        match incr {
            Some(true) => stats.observed_sat += 1,
            Some(false) => stats.observed_unsat += 1,
            None => {}
        }

        if incr.is_none() {
            let repro = dump_repro(
                "UNEXPECTED UNKNOWN",
                config,
                seed,
                round,
                num_vars,
                &sol,
                &db,
                &assumptions,
            );
            panic!(
                "{repro}\nunknown reason = {:?}\n\
                 BUG: this uninterrupted finite query must complete with SAT or UNSAT",
                solver.last_unknown_reason(),
            );
        }

        // Whenever a SAT model escapes to the caller, it MUST satisfy every
        // accumulated original clause. Catches false-SAT (bad model
        // reconstruction) regardless of SAT/adversarial round kind.
        if let AssumeResult::Sat(model) = &raw {
            if let Some(ci) = model_violation(&db, model) {
                let repro = dump_repro(
                    "FALSE-SAT (returned model violates a clause)",
                    config,
                    seed,
                    round,
                    num_vars,
                    &sol,
                    &db,
                    &assumptions,
                );
                panic!(
                    "{repro}\nreturned model = {model:?}\n\
                     BUG: reported SAT but the returned model violates clause index {ci} \
                     ({:?}).",
                    db[ci]
                );
            }
        }

        if !adversarial {
            // ORACLE 1: provably SAT (planted sol satisfies db + assumptions),
            // so the ONLY sound verdict is SAT. UNSAT is a false-UNSAT; Unknown
            // is a completeness failure / internal downgrade on a trivially
            // solvable query (the fresh solver solves it — see below).
            stats.guaranteed_sat_rounds += 1;
            debug_assert!(
                db.iter().all(|c| clause_sat(c, &sol)),
                "planted invariant violated"
            );
            match incr {
                // SOUNDNESS FAILURE: a definite UNSAT on a provably-SAT query is a
                // false-UNSAT — a WRONG verdict. This is what the soak exists to catch.
                Some(false) => {
                    let repro = dump_repro(
                        "FALSE-UNSAT (planted-solution oracle)",
                        config,
                        seed,
                        round,
                        num_vars,
                        &sol,
                        &db,
                        &assumptions,
                    );
                    let fresh = fresh_verdict(num_vars, &db, &assumptions);
                    panic!(
                        "{repro}\nincremental verdict = FALSE, fresh-solver verdict = {fresh:?}\n\
                         BUG: the planted assignment `sol` satisfies every accumulated clause \
                         AND every assumption, so this query is provably SAT, yet the \
                         incrementally-driven solver returned UNSAT (a wrong verdict)."
                    );
                }
                None => unreachable!("Unknown rejected above"),
                Some(true) => {}
            }
        } else {
            // ORACLE 2: incremental vs fresh differential (+ brute adjudication).
            stats.adversarial_rounds += 1;
            let i = incr.expect("Unknown rejected above");
            let f = fresh_verdict(num_vars, &db, &assumptions).unwrap_or_else(|| {
                let repro = dump_repro(
                    "FRESH SOLVER RETURNED UNKNOWN",
                    config,
                    seed,
                    round,
                    num_vars,
                    &sol,
                    &db,
                    &assumptions,
                );
                panic!("{repro}\nBUG: uninterrupted fresh solve must return SAT or UNSAT");
            });
            if i == f {
                stats.differential_agree += 1;
            } else {
                // Disagreement — adjudicate with brute force if feasible.
                let truth = if brute_ok {
                    Some(brute_force_sat(num_vars, &db, &assumptions))
                } else {
                    None
                };
                let repro = dump_repro(
                    "INCREMENTAL vs FRESH DISAGREEMENT",
                    config,
                    seed,
                    round,
                    num_vars,
                    &sol,
                    &db,
                    &assumptions,
                );
                panic!(
                    "{repro}\nincremental={} fresh={} brute_force_truth={:?}\n\
                     BUG: incremental and from-scratch solves of the SAME clause set + \
                     assumptions disagree. If incremental=UNSAT this is the target \
                     false-UNSAT.",
                    if i { "SAT" } else { "UNSAT" },
                    if f { "SAT" } else { "UNSAT" },
                    truth.map(|t| if t { "SAT" } else { "UNSAT" }),
                );
            }
        }

        // Grow the clause DB (still planted-satisfiable) for the next round.
        for _ in 0..add_per_round {
            let l = rand_len(&mut rng);
            let c = planted_clause(&mut rng, num_vars, l, &sol);
            solver.add_clause(c.clone());
            db.push(c);
        }
    }
}

/// Optional environment scaling for heavy local searches:
///   AY_FUZZ_SEED_MUL   multiplies the seed count (default 1)
///   AY_FUZZ_ROUND_MUL  multiplies the round count (default 1)
/// The default (unset) run stays cheap for CI.
fn env_mul(name: &str) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .filter(|&v| v >= 1)
        .unwrap_or(1)
}

fn run_campaign(
    label: &str,
    configs: &[Config],
    num_vars: usize,
    base_seeds: u64,
    base_rounds: usize,
    init_clauses: usize,
    add_per_round: usize,
    adversarial_pct: u64,
) {
    let seeds = base_seeds * env_mul("AY_FUZZ_SEED_MUL");
    let rounds = base_rounds * (env_mul("AY_FUZZ_ROUND_MUL") as usize);
    let mut stats = CampaignStats::default();
    for &config in configs {
        for seed in 0..seeds {
            run_seed(
                config,
                seed,
                num_vars,
                rounds,
                init_clauses,
                add_per_round,
                adversarial_pct,
                &mut stats,
            );
        }
    }
    eprintln!(
        "[{label}] PASS: no false-UNSAT / disagreement.\n  \
         configs={} seeds={seeds} num_vars={num_vars} rounds={rounds} \
         init_clauses={init_clauses} add/round={add_per_round} adversarial={adversarial_pct}%\n  \
         guaranteed-SAT rounds verified = {} (no false-UNSAT or Unknown)\n  \
         adversarial rounds = {} (incr-vs-fresh differential; agreements = {})\n  \
         observed verdicts: SAT = {}, UNSAT = {}",
        configs.len(),
        stats.guaranteed_sat_rounds,
        stats.adversarial_rounds,
        stats.differential_agree,
        stats.observed_sat,
        stats.observed_unsat,
    );
    // Coverage sanity: the search must actually exercise UNSAT verdicts,
    // otherwise it proves nothing about the false-UNSAT path.
    assert!(
        stats.observed_unsat > 0,
        "[{label}] search never produced any UNSAT verdict — not stressing the \
         false-UNSAT path; tune adversarial_pct / density"
    );
}

// ---------------------------------------------------------------------------
// Focused regression for an incremental vivify × subsumption defect.
//
// ROOT CAUSE (root-caused with a concrete witness num_vars=12 seed=2483 round=1;
// NOT the BVE model-reconstruction it was originally suspected to be —
// reconstruction_len==0 at the failure, so witness replay is not involved). It
// is a 2-watched-literal (2WL) invariant violation from the VIVIFY x SUBSUMPTION
// interaction on the incremental (`has_been_incremental`) path, where destructive
// inprocessing (BVE/BCE/...) is already gated OFF:
//   1. Subsumption self-subsuming-strengthens an original clause IN PLACE (sound),
//      attaching watches while its literals are unassigned.
//   2. Vivification then fixes BOTH of that clause's watched literals false at
//      level 0 (via binary reasons) WITHOUT repairing its watches or propagating
//      the now-implied level-0 unit. `qhead` advances past those assignments, so
//      BCP never re-examines the clause — it is stranded on two level-0-false
//      watches.
//   3. Search later decides the remaining literal true (level 1); the clause is
//      fully falsified but invisible to BCP => a spurious full assignment.
// Bisection is decisive: the trigger needs BOTH vivify AND subsume; disabling
// either kills it; BVE/BCE/probe are irrelevant.
//
// The always-on `finalize_sat` gate (#8819) contained the historical failure by
// returning Unknown/`InvalidSatModel`. The regression below requires the
// production watch repair to prevent that downgrade altogether.
// ---------------------------------------------------------------------------

/// Drive one PreprocessHeavy solver and return the round index at which the
/// `finalize_sat` gate first fires `InvalidSatModel`, together with the exact
/// accumulated clause DB + assumptions + planted solution at that point.
/// Also asserts, at every round, that NO unsound verdict escapes.
#[allow(clippy::type_complexity)]
fn probe_vivify_subsume_corruption(
    num_vars: usize,
    seed: u64,
    rounds: usize,
    init_clauses: usize,
    add_per_round: usize,
    adversarial_pct: u64,
) -> Option<(usize, Vec<bool>, Vec<Vec<Literal>>, Vec<Literal>)> {
    let mut rng = Rng::new(seed ^ ((Config::PreprocessHeavy as u64).wrapping_mul(0x9E37)));
    let sol: Vec<bool> = (0..num_vars).map(|_| rng.boolean()).collect();
    let mut solver = Solver::new(num_vars);
    Config::PreprocessHeavy.apply(&mut solver);
    let mut db: Vec<Vec<Literal>> = Vec::new();
    let rand_len = |rng: &mut Rng| 2 + rng.below(3);
    for _ in 0..init_clauses {
        let l = rand_len(&mut rng);
        let c = planted_clause(&mut rng, num_vars, l, &sol);
        solver.add_clause(c.clone());
        db.push(c);
    }
    for round in 0..rounds {
        let adversarial = rng.chance(adversarial_pct);
        let n_assume = rng.below(num_vars / 3 + 1);
        let mut seen = HashSet::new();
        let mut assumptions = Vec::with_capacity(n_assume);
        while assumptions.len() < n_assume {
            let v = rng.below(num_vars);
            if seen.insert(v) {
                let pol = if adversarial { rng.boolean() } else { sol[v] };
                assumptions.push(lit(v, pol));
            }
        }
        let raw = solver
            .solve_with_assumptions_interruptible(&assumptions, || false)
            .into_inner();

        // Soundness invariants that MUST hold regardless of internal corruption:
        // (1) no returned SAT model may violate an accumulated clause;
        if let AssumeResult::Sat(model) = &raw {
            assert!(
                model_violation(&db, model).is_none(),
                "seed={seed} round={round}: escaped false-SAT (model violates a clause)"
            );
        }
        // (2) a provably-SAT (planted) query must never come back UNSAT.
        if !adversarial {
            assert!(
                !raw.is_unsat(),
                "seed={seed} round={round}: escaped false-UNSAT on a planted-SAT query"
            );
        }

        if solver.last_unknown_reason() == Some(SatUnknownReason::InvalidSatModel) {
            return Some((round, sol, db, assumptions));
        }

        for _ in 0..add_per_round {
            let l = rand_len(&mut rng);
            let c = planted_clause(&mut rng, num_vars, l, &sol);
            solver.add_clause(c.clone());
            db.push(c);
        }
    }
    None
}

/// Bounded regression for the incremental vivify × subsumption 2WL defect.
///
/// The former ignored test searched 36,000 `(num_vars, seed)` pairs even though
/// the minimal deterministic witness is known. Exercise only that witness and
/// its first two rounds. [`probe_vivify_subsume_corruption`] asserts on every
/// round that no false SAT or false UNSAT verdict escapes. The historical
/// failure returned `InvalidSatModel` at round 1; the root fix must prevent any
/// such trigger.
#[test]
#[timeout(30_000)]
fn incremental_vivify_subsume_soundness_regression() {
    let trigger = probe_vivify_subsume_corruption(
        /* num_vars */ 12, /* seed */ 2483, /* rounds */ 2,
        /* init_clauses */ 60, /* add_per_round */ 2, /* adversarial_pct */ 60,
    )
    .map(|(round, _, _, _)| round);

    assert_eq!(
        trigger, None,
        "vivification left a clause stranded on level-0-false watches"
    );
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

/// Sweep rewrites an original clause, BCE removes the rewritten clause, and
/// BVE later eliminates its blocking variable. The BCE witness must remain on
/// the reconstruction stack so the original clause is restored.
#[test]
#[timeout(30_000)]
fn preprocess_heavy_seed_15_reconstruction_regression() {
    let mut stats = CampaignStats::default();
    run_seed(
        Config::PreprocessHeavy,
        /* seed */ 15,
        /* num_vars */ 16,
        /* rounds */ 1,
        /* init_clauses */ 64,
        /* add_per_round */ 0,
        /* adversarial_pct */ 70,
        &mut stats,
    );
}

/// Vivification shortens an original clause before BCE removes it and BVE
/// later eliminates the same blocking variable. Retaining the earlier BCE
/// witness prevents a model-reconstruction downgrade to `InvalidSatModel`.
#[test]
#[timeout(30_000)]
fn preprocess_heavy_seed_18_reconstruction_regression() {
    let mut stats = CampaignStats::default();
    run_seed(
        Config::PreprocessHeavy,
        /* seed */ 18,
        /* num_vars */ 40,
        /* rounds */ 1,
        /* init_clauses */ 120,
        /* add_per_round */ 0,
        /* adversarial_pct */ 55,
        &mut stats,
    );
}

/// Large-variable planted campaign across all three configs. The planted
/// oracle makes every non-adversarial round a provable SAT, so any incremental
/// UNSAT there is a definitive false-UNSAT. Adversarial rounds are checked
/// against a fresh from-scratch solve.
#[test]
#[timeout(300_000)]
fn false_unsat_planted_campaign_large() {
    run_campaign(
        "planted-large",
        &[
            Config::Ic3Mode,
            Config::IncrementalMode,
            Config::PreprocessHeavy,
        ],
        /* num_vars */ 40,
        /* seeds */ 20,
        /* rounds */ 18,
        /* init_clauses */ 120, // ratio 3.0, constraint-dense
        /* add_per_round */ 2,
        /* adversarial_pct */ 55,
    );
}

/// Small-variable differential campaign with brute-force ground truth always
/// available to adjudicate any incremental-vs-fresh disagreement. Focused on
/// the preprocessing-heavy prime suspect and the real IC3 mode.
#[test]
#[timeout(300_000)]
fn false_unsat_differential_small_bruteforce() {
    run_campaign(
        "differential-small",
        &[Config::PreprocessHeavy, Config::Ic3Mode],
        /* num_vars */ 18,
        /* seeds */ 40,
        /* rounds */ 20,
        /* init_clauses */ 70, // ratio ~3.9
        /* add_per_round */ 2,
        /* adversarial_pct */ 60,
    );
}

/// High-density stress: clause/var ratio near the phase transition where
/// assumption queries flip between SAT and UNSAT most often — the regime the
/// bug report calls out ("constraint-dense problems").
#[test]
#[timeout(300_000)]
fn false_unsat_dense_phase_transition() {
    run_campaign(
        "dense-phase-transition",
        &[
            Config::PreprocessHeavy,
            Config::IncrementalMode,
            Config::Ic3Mode,
        ],
        /* num_vars */ 16,
        /* seeds */ 30,
        /* rounds */ 25,
        /* init_clauses */ 64, // ratio 4.0
        /* add_per_round */ 3,
        /* adversarial_pct */ 70,
    );
}
