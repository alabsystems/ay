// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reproduction: scoped-BVE variable REUSE *without pop* → false verdict.
//!
//! Root cause (confirmed): `set_ic3_mode()` keeps scoped BVE enabled
//! (`incremental.rs` `set_bve_enabled(true)`). Inside a `push()` scope, scoped
//! BVE can eliminate a scope-local variable `t`: it deletes `t`'s original
//! clauses from the arena and adds the resolvent, which encodes `∃t.(t's
//! clauses)` and is strictly WEAKER than the originals. If a later clause
//! reactivates `t` *without an intervening `pop()`*, `add_clause` only re-marks
//! `t` Active — it does NOT restore `t`'s BVE-deleted clauses. The between-solves
//! reset then decides whether to rebuild the arena from the original ledger:
//!   `can_use_incremental_reset()` used to return `true` unconditionally in
//!   ic3_mode (fast path, no rebuild), so the next solve searched the *projected*
//!   (weaker) arena. On a query the REAL formula makes UNSAT, the projected arena
//!   is still SAT, and the solver returns that spurious model as SAT — an
//!   ESCAPING false-SAT (observed: `Sat([...])` where the exhaustive truth is
//!   UNSAT). For an IC3/PDR consumer this is a wrong verdict that manifests as a
//!   spurious counterexample / false result.
//!
//! The fix (preprocess_reset.rs `can_use_incremental_reset`): in ic3_mode, force
//! a full ledger-rebuild reset when the reconstruction stack is non-empty, so
//! the arena is restored to the real formula before the next solve.
//!
//! Oracle: BRUTE FORCE ground truth. The formulas are tiny, so every query's
//! truth is computed exhaustively and the incremental scoped solver must match
//! it. On these formulas the solver has no resource budget, so an `Unknown` can
//! only come from the scoped-BVE arena divergence and is itself a wrong verdict.
//!
//! Run: cargo test -p ay-sat --lib scoped_bve_var_reuse -- --nocapture

use crate::solver::Solver;
use crate::{AssumeResult, Literal, Variable};

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}
fn neg(v: u32) -> Literal {
    Literal::negative(Variable(v))
}
fn lit(v: u32, positive: bool) -> Literal {
    if positive {
        pos(v)
    } else {
        neg(v)
    }
}

/// Force the incremental-inprocessing scheduling gates open so the next solve
/// runs `run_incremental_inprocessing` (including scoped BVE). Identical to the
/// helper in `scoped_bve_pop_soundness.rs`.
fn open_inprocessing_gates(s: &mut Solver) {
    s.cold.lifetime_conflicts = 100;
    s.cold.next_inprobe_conflict = 0;
    s.cold.last_inprobe_reduction = 0;
    s.cold.num_reductions = 1;
    s.inproc_ctrl.bve.enabled = true;
    s.inproc_ctrl.bve.next_conflict = 0;
}

fn clause_sat(clause: &[Literal], assign: &[bool]) -> bool {
    clause
        .iter()
        .any(|l| assign.get(l.variable().index()).copied().unwrap_or(false) == l.is_positive())
}

/// Exhaustive ground truth: is `real ∧ assumptions` satisfiable?
fn brute_force_sat(num_vars: usize, real: &[Vec<Literal>], assumptions: &[Literal]) -> bool {
    let mut assign = vec![false; num_vars];
    'outer: for mask in 0u64..(1u64 << num_vars) {
        for (i, a) in assign.iter_mut().enumerate() {
            *a = (mask >> i) & 1 == 1;
        }
        for a in assumptions {
            if assign[a.variable().index()] != a.is_positive() {
                continue 'outer;
            }
        }
        for c in real {
            if !clause_sat(c, &assign) {
                continue 'outer;
            }
        }
        return true;
    }
    false
}

fn max_index(real: &[Vec<Literal>], assumptions: &[Literal]) -> usize {
    real.iter()
        .flatten()
        .chain(assumptions.iter())
        .map(|l| l.variable().index())
        .max()
        .unwrap_or(0)
}

/// Classify an incremental verdict against brute-force truth. Returns Some(msg)
/// if the verdict is wrong (false-SAT, false-UNSAT, or an Unknown downgrade).
fn check(incr: &AssumeResult, truth: bool) -> Option<String> {
    match incr {
        AssumeResult::Sat(_) if !truth => {
            Some("returned SAT but real formula + assumptions is UNSAT (false-SAT)".into())
        }
        AssumeResult::Unsat(..) if truth => {
            Some("returned UNSAT but real formula + assumptions is SAT (FALSE-UNSAT)".into())
        }
        AssumeResult::Sat(_) | AssumeResult::Unsat(..) => None,
        _ => Some(format!(
            "returned Unknown (finalize downgrade from scoped-BVE arena divergence) while the \
             real formula + assumptions is definitively {}",
            if truth { "SAT" } else { "UNSAT" }
        )),
    }
}

/// Minimal, fully deterministic reproduction.
///
/// Base:      (v2 ∨ v3)                     — independent, satisfiable
/// Scope 1:   (t ∨ ¬v0), (¬t ∨ ¬v1)         — t has 2 occurrences → BVE target
///            scoped BVE eliminates t, leaving the resolvent (¬v0 ∨ ¬v1).
/// Reuse:     add (t ∨ ¬v4) WITHOUT pop     — reactivates t; assuming v4 forces t.
///
/// Query assumptions {v1=true, v4=true}:
///   REAL:  v4 ⇒ t (from t∨¬v4);  t ∧ v1 falsifies (¬t ∨ ¬v1)  ⇒ UNSAT.
///   PROJECTED (buggy arena, t's originals gone): (¬v0∨¬v1) ∧ (t∨¬v4) with
///          v1,v4 ⇒ needs v0=false, t=true ⇒ SAT — a model that violates the
///          real clause (¬t∨¬v1). The finalize gate catches it ⇒ Unknown.
///
/// So: FIXED ⇒ UNSAT (correct); BUGGY ⇒ Unknown/SAT (wrong).
#[test]
fn scoped_bve_var_reuse_deterministic_false_verdict() {
    let mut s = Solver::new(6);
    s.set_ic3_mode();

    let mut real: Vec<Vec<Literal>> = Vec::new();
    let base = vec![pos(2), pos(3)];
    s.add_clause(base.clone());
    real.push(base);

    s.push();
    assert!(s.has_scoped_bve(), "push must enable scoped BVE");
    let t = s.new_var_internal().index() as u32;

    let c1 = vec![pos(t), neg(0)]; // t ∨ ¬v0
    let c2 = vec![neg(t), neg(1)]; // ¬t ∨ ¬v1
    s.add_clause(c1.clone());
    s.add_clause(c2.clone());
    real.push(c1);
    real.push(c2);

    open_inprocessing_gates(&mut s);
    let recon_before = s.inproc.reconstruction.len();
    let r1 = s.solve_incremental_ic3(&[]).into_inner();
    assert!(r1.is_sat(), "scope-1 formula must be SAT, got {r1:?}");
    let eliminated = s.inproc.reconstruction.len() > recon_before;
    assert!(
        eliminated,
        "scoped BVE did not eliminate t (reconstruction stack did not grow) — the \
         reproduction precondition is not met"
    );

    // Reactivate t WITHOUT pop.
    let nc = vec![pos(t), neg(4)]; // t ∨ ¬v4
    s.add_clause(nc.clone());
    real.push(nc);

    // Query that the REAL formula makes UNSAT via t's (deleted) clauses.
    let assumptions = vec![pos(1), pos(4)]; // v1 = true, v4 = true
    open_inprocessing_gates(&mut s);
    let incr = s.solve_incremental_ic3(&assumptions).into_inner();

    let num_vars = max_index(&real, &assumptions) + 1;
    let truth = brute_force_sat(num_vars, &real, &assumptions);
    assert!(!truth, "sanity: brute force says this query is UNSAT");

    if let Some(msg) = check(&incr, truth) {
        panic!(
            "SCOPED-BVE VAR-REUSE FALSE VERDICT (deterministic):\n  {msg}\n  \
             incr={incr:?}, brute-force truth=UNSAT\n  \
             assumptions={assumptions:?}\n  real={real:?}\n\n\
             After scoped BVE eliminated t and (t ∨ ¬v4) reactivated it WITHOUT pop(), the \
             ic3_mode incremental reset skipped the ledger rebuild and searched the projected \
             (weaker) formula, which is SAT where the real formula is UNSAT."
        );
    }
}

// ---------------------------------------------------------------------------
// Randomized sweep around the same pattern (base-only assumptions).
// ---------------------------------------------------------------------------

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_add(0x1234_5678_9abc_def0))
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn boolean(&mut self) -> bool {
        self.next() & 1 == 0
    }
}

fn planted_clause(rng: &mut Rng, cands: &[u32], len: usize, sol: &[bool]) -> Vec<Literal> {
    use std::collections::HashSet;
    let len = len.min(cands.len()).max(1);
    let mut seen = HashSet::new();
    let mut vs = Vec::with_capacity(len);
    while vs.len() < len {
        let v = cands[rng.below(cands.len())];
        if seen.insert(v) {
            vs.push(v);
        }
    }
    let mut c: Vec<Literal> = vs.iter().map(|&v| lit(v, rng.boolean())).collect();
    if !clause_sat(&c, sol) {
        let i = rng.below(c.len());
        let v = c[i].variable().index();
        c[i] = lit(v as u32, sol[v]);
    }
    c
}

/// One randomized case, mirroring the deterministic pattern but with random
/// base literals and several probe queries. Assumptions are over BASE vars only
/// (never the eliminated scope var, which would hit an internal decided-removed
/// -variable guard). Returns (eliminated, unsat_truths, first_violation).
fn run_case(seed: u64) -> (bool, usize, Option<String>) {
    let mut rng = Rng::new(seed);
    let n_base = 5 + rng.below(4); // 5..=8
    let sol_len = n_base + 8;
    let sol: Vec<bool> = (0..sol_len).map(|_| rng.boolean()).collect();

    let mut s = Solver::new(n_base);
    s.set_ic3_mode();
    let base_cands: Vec<u32> = (0..n_base as u32).collect();
    let mut real: Vec<Vec<Literal>> = Vec::new();

    for _ in 0..(n_base + rng.below(n_base)) {
        let len = 2 + rng.below(2);
        let c = planted_clause(&mut rng, &base_cands, len, &sol);
        s.add_clause(c.clone());
        real.push(c);
    }

    s.push();
    let t = s.new_var_internal().index() as u32;
    // t-clauses: (t ∨ La), (¬t ∨ Lb) over two base vars a, b. Pin La, Lb to the
    // planted solution so `sol` satisfies them (via La/Lb) regardless of sol[t],
    // keeping the whole formula planted-satisfiable. The divergence is then
    // driven by ASSUMPTIONS that falsify La/Lb.
    let a = base_cands[rng.below(base_cands.len())];
    let b = base_cands[rng.below(base_cands.len())];
    let pa = sol[a as usize];
    let pb = sol[b as usize];
    let c1 = vec![pos(t), lit(a, pa)];
    let c2 = vec![neg(t), lit(b, pb)];
    s.add_clause(c1.clone());
    s.add_clause(c2.clone());
    real.push(c1);
    real.push(c2);

    open_inprocessing_gates(&mut s);
    let recon_before = s.inproc.reconstruction.len();
    let r1 = s.solve_incremental_ic3(&[]).into_inner();
    if !r1.is_sat() {
        return (
            false,
            0,
            Some(format!("seed={seed}: scope-1 not SAT ({r1:?})")),
        );
    }
    let eliminated = s.inproc.reconstruction.len() > recon_before;

    // Reactivate t via (t ∨ Lc) so assuming ¬Lc forces t = true. Pin Lc to sol.
    let c = base_cands[rng.below(base_cands.len())];
    let pc = sol[c as usize];
    let nc = vec![pos(t), lit(c, pc)];
    s.add_clause(nc.clone());
    real.push(nc);

    let num_vars = max_index(&real, &[]) + 1;
    let mut unsat_truths = 0usize;

    // Targeted probe: assume c to force t=true, and b to the side that falsifies
    // Lb (so (¬t ∨ Lb) forces ¬t, contradiction) — this is the divergence
    // pattern. Then several random base-only probes.
    let mut assumption_sets: Vec<Vec<Literal>> = Vec::new();
    // Divergence-targeting set: force t via c, falsify Lb via b.
    assumption_sets.push(vec![lit(c, !pc), lit(b, !pb)]);
    // Symmetric set: force ¬t via ... (t ∨ La) with a falsifying La forces t? no;
    // just add a couple randomized base-only sets.
    for _ in 0..5 {
        let mut set = Vec::new();
        let k = 1 + rng.below(3);
        for _ in 0..k {
            let v = base_cands[rng.below(base_cands.len())];
            set.push(lit(v, rng.boolean()));
        }
        assumption_sets.push(set);
    }

    for assumptions in &assumption_sets {
        open_inprocessing_gates(&mut s);
        let incr = s.solve_incremental_ic3(assumptions).into_inner();
        let truth = brute_force_sat(num_vars, &real, assumptions);
        if !truth {
            unsat_truths += 1;
        }
        if let Some(msg) = check(&incr, truth) {
            return (
                eliminated,
                unsat_truths,
                Some(format!(
                    "seed={seed}: {msg}\n  incr={incr:?} truth={}\n  eliminated={eliminated} \
                     t={t} num_vars={num_vars}\n  assumptions={assumptions:?}\n  real={real:?}",
                    if truth { "SAT" } else { "UNSAT" }
                )),
            );
        }
    }

    (eliminated, unsat_truths, None)
}

/// Randomized sweep. FIXED tree ⇒ passes; BUGGY tree ⇒ fails.
#[test]
fn scoped_bve_var_reuse_without_pop_is_sound() {
    let mut eliminated_cases = 0usize;
    let mut unsat_truths = 0usize;
    let seeds = 2000u64;
    for seed in 0..seeds {
        let (elim, ut, violation) = run_case(seed);
        eliminated_cases += usize::from(elim);
        unsat_truths += ut;
        if let Some(v) = violation {
            panic!(
                "SCOPED-BVE VAR-REUSE FALSE VERDICT reproduced:\n  {v}\n\n\
                 Re-run: cargo test -p ay-sat --lib scoped_bve_var_reuse -- --nocapture"
            );
        }
    }
    assert!(
        eliminated_cases > 0,
        "scoped BVE never eliminated a scope var — path not exercised"
    );
    assert!(
        unsat_truths > 0,
        "no query drove the real formula UNSAT — divergence direction not stressed"
    );
    eprintln!(
        "scoped_bve_var_reuse: PASS — {seeds} seeds, {eliminated_cases} eliminated a scope var, \
         {unsat_truths} UNSAT-truth probes; incremental scoped solver matched brute-force truth."
    );
}
