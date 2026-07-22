// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inc5 GATE TESTS: same-solver ext→ext restart across a clause-arena rebuild.
//!
//! Design brief: the development design notes
//! The stale-clause-arena hazard (mechanism: preprocess_reset.rs:519-536,
//! mitigation :534-536 / #inc-rebuild-reasons, plus the pending_theory_conflict
//! clear at :380 / #inc-pending-conflict, commit 1ceec34cb9):
//!
//!   Extension theory lemmas added at scope depth 0 are learned-yet-axiomatic
//!   clauses (`add_theory_lemma` → `add_clause_db_checked(lits, learned=true, ..)`)
//!   that are ABSENT from the original-clause ledger and unswept by pop GC.
//!   They propagate root facts whose `VarData.reason` holds a raw arena offset.
//!   When a later solve entry rebuilds the arena (`self.arena = ClauseArena::new()`
//!   at preprocess_reset.rs:519), every old offset is invalidated; a surviving
//!   stale ref (a root-fact reason, or the `pending_theory_conflict` ClauseRef)
//!   dereferenced in `cdcl_loop_impl` reads far out of bounds (observed under
//!   AY_LRA_EAGER_LAZY: arena len 6, index ~174M → panic).
//!
//! What triggers a rebuild at solve entry (`reset_search_state`):
//!   - destructive: `active_original_count != ledger_count` OR
//!     `cold.inprocessing_modified_clause_db` (BVE/BCE/congruence/decompose;
//!     set at mutate_delete.rs / congruence/mod.rs) — drops learned clauses;
//!   - L0-GC: `cold.l0_gc_modified_clause_db` (set at inprocessing.rs:555/:595)
//!     — preserves learned clauses at NEW offsets.
//! These tests force each flag directly between solves (same pattern as
//! tests/original_clause_ledger.rs:233); the flags are read ONLY by the rebuild
//! census, and they are cleared ONLY inside the rebuild branch
//! (preprocess_reset.rs:558-559), so "flag set before solve N+1, clear after"
//! is airtight evidence that the rebuild branch executed.
//!
//! GATE SEMANTICS (brief §Hazard correction): the eager UFLIA arm re-enters
//! `reset_search_state` every round on a persistent solver. If any test here
//! panics, Inc5 must switch to an isolated-solver embodiment. If they pass,
//! the NO_REASON normalization covers the ext→ext restart direction and Inc5
//! may fuse arms on the shared solver.
//!
//! The UFLIA-style scenario (propositional skeleton of UF congruence + a LIA
//! bound atom):
//!   x0 = (a=b)   x1 = (b=c)   x2 = (a=c)      [transitivity target]
//!   x3 = (f(a)=f(c))                          [congruence target]
//!   x4 = (f(a) < f(c))                        [LIA atom, contradicts x3]
//!   x5, x6 = free Boolean vars forcing at least one decision
//! Lemmas are deliberately TERNARY: binary-clause propagations are stored as
//! packed binary-literal reasons (#8034), not arena offsets — the hazard
//! shape requires a real arena ClauseRef in `VarData.reason`.

use super::*;
use crate::extension::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};
use crate::solver::var_data::is_clause_reason;

const EQ_AB: u32 = 0; // a=b (unit original)
const EQ_BC: u32 = 1; // b=c (unit original)
const EQ_AC: u32 = 2; // a=c (theory-derived: transitivity)
const EQ_FAFC: u32 = 3; // f(a)=f(c) (theory-derived: congruence)
const LT_FAFC: u32 = 4; // f(a)<f(c) (LIA atom; theory-refuted)
const FREE_A: u32 = 5;
const FREE_B: u32 = 6;
const NUM_VARS: usize = 7;

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}
fn neg(v: u32) -> Literal {
    Literal::negative(Variable(v))
}

/// The three UFLIA-style theory lemmas. Layout: premises first (negated
/// occurrences), conclusion last. All ternary (see module docs).
fn uflia_lemmas() -> [Vec<Literal>; 3] {
    [
        // transitivity: a=b ∧ b=c → a=c
        vec![neg(EQ_AB), neg(EQ_BC), pos(EQ_AC)],
        // congruence: a=c → f(a)=f(c); premise a=b padded in to keep it ternary
        vec![neg(EQ_AB), neg(EQ_AC), pos(EQ_FAFC)],
        // LIA bound: a=c ∧ f(a)=f(c) → ¬(f(a)<f(c))
        vec![neg(EQ_AC), neg(EQ_FAFC), neg(LT_FAFC)],
    ]
}

/// Minimal eager DPLL(T)-style extension: emits each lemma once per solve,
/// as soon as all its premise literals are falsified (premises true), so the
/// lemma clause immediately propagates its conclusion — at level 0 when the
/// premises are root facts. `init()` resets the per-solve emission state so
/// the same extension value can drive repeated solves (persistent-solver
/// round pattern).
struct UfliaChainExt {
    emitted: [bool; 3],
    /// Extra copies of the transitivity lemma emitted once per solve. Used by
    /// the pending-conflict regression test to make the solve-1 arena
    /// substantially larger than the rebuilt arena, so a stale top-of-arena
    /// offset is genuinely OUT of bounds after the rebuild (the incident
    /// shape: old arena ~174M words, rebuilt arena 6 words).
    padding: u32,
    padding_emitted: bool,
}

impl UfliaChainExt {
    fn new() -> Self {
        Self {
            emitted: [false; 3],
            padding: 0,
            padding_emitted: false,
        }
    }
}

impl Extension for UfliaChainExt {
    fn init(&mut self) {
        self.emitted = [false; 3];
        self.padding_emitted = false;
    }

    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        let mut out: Vec<Vec<Literal>> = Vec::new();
        if self.padding > 0
            && !self.padding_emitted
            && ctx.lit_value(pos(EQ_AB)) == Some(true)
            && ctx.lit_value(pos(EQ_BC)) == Some(true)
        {
            self.padding_emitted = true;
            let transitivity = uflia_lemmas()[0].clone();
            for _ in 0..self.padding {
                out.push(transitivity.clone());
            }
        }
        for (i, lemma) in uflia_lemmas().iter().enumerate() {
            if self.emitted[i] {
                continue;
            }
            let premises_hold = lemma[..lemma.len() - 1]
                .iter()
                .all(|l| ctx.lit_value(*l) == Some(false));
            if premises_hold {
                self.emitted[i] = true;
                out.push(lemma.clone());
            }
        }
        if out.is_empty() {
            ExtPropagateResult::none()
        } else {
            ExtPropagateResult::clauses(out)
        }
    }

    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        !self.emitted.iter().all(|e| *e)
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        // Model-repair final check: a lemma violated by the full model is
        // returned as a (theory-valid) blocking clause. Unreachable once the
        // lemma clauses are in the DB; present for verdict soundness.
        for lemma in uflia_lemmas() {
            if lemma.iter().all(|l| ctx.lit_value(*l) == Some(false)) {
                return ExtCheckResult::Conflict(lemma.clone());
            }
        }
        ExtCheckResult::Sat
    }
}

/// Original (ledger) clauses: the two equality units feeding the lemma chain,
/// plus two free-var clauses so SAT needs at least one real decision
/// (models: x6 forced true, x5 free).
fn add_uflia_originals(solver: &mut Solver) {
    assert!(solver.add_clause(vec![pos(EQ_AB)]));
    assert!(solver.add_clause(vec![pos(EQ_BC)]));
    assert!(solver.add_clause(vec![pos(FREE_A), pos(FREE_B)]));
    assert!(solver.add_clause(vec![neg(FREE_A), pos(FREE_B)]));
}

fn assert_uflia_sat_model(model: &[bool], ctx: &str) {
    assert!(model.len() >= NUM_VARS, "{ctx}: short model");
    assert!(model[EQ_AB as usize], "{ctx}: unit original x0 (a=b)");
    assert!(model[EQ_BC as usize], "{ctx}: unit original x1 (b=c)");
    assert!(model[EQ_AC as usize], "{ctx}: transitivity fact x2 (a=c)");
    assert!(
        model[EQ_FAFC as usize],
        "{ctx}: congruence fact x3 (f(a)=f(c))"
    );
    assert!(
        !model[LT_FAFC as usize],
        "{ctx}: LIA atom x4 must be refuted by the lemma chain"
    );
    assert!(
        model[FREE_B as usize],
        "{ctx}: x6 forced by free-var clauses"
    );
}

/// Verify the hazard shape is armed after an extension solve: the
/// theory-derived facts sit on the level-0 trail with `VarData.reason`
/// holding raw arena clause offsets (the refs a subsequent arena rebuild
/// invalidates). Returns the stale-ref candidate ClauseRef of x2's reason.
fn assert_level0_arena_reason_facts(solver: &Solver, ctx: &str) -> ClauseRef {
    for v in [EQ_AC, EQ_FAFC, LT_FAFC] {
        let idx = v as usize;
        assert!(
            solver.var_is_assigned(idx),
            "{ctx}: theory fact x{v} must remain assigned after solve"
        );
        let vd = solver.var_data[idx];
        assert_eq!(
            vd.level, 0,
            "{ctx}: theory fact x{v} must be a root (level-0) fact"
        );
        assert!(
            is_clause_reason(vd.reason),
            "{ctx}: theory fact x{v} must carry an arena clause reason \
             (got {:#x}); ternary lemma propagations must not degrade to \
             binary/NO_REASON or the test no longer arms the hazard",
            vd.reason
        );
    }
    ClauseRef(solver.var_data[EQ_AC as usize].reason)
}

/// PRIMARY GATE: ext→ext restart on one persistent solver across BOTH arena
/// rebuild flavors (L0-GC-preserving, then destructive). Must not panic and
/// must stay SAT with the theory facts intact each round — three extension
/// rounds total, mirroring the eager-arm round lifecycle.
#[test]
fn inc5_gate_ext_to_ext_restart_survives_arena_rebuilds() {
    let mut solver = Solver::new(NUM_VARS);
    add_uflia_originals(&mut solver);
    let mut ext = UfliaChainExt::new();

    // Round 1: arm the hazard (level-0 lemma facts with arena reasons).
    let r1 = solver.solve_with_extension(&mut ext).into_inner();
    let SatResult::Sat(m1) = r1 else {
        panic!("round 1 must be SAT, got {r1:?}");
    };
    assert_uflia_sat_model(&m1, "round 1");
    assert_level0_arena_reason_facts(&solver, "round 1");

    // Force the L0-GC rebuild condition (real setter: inprocessing.rs:555).
    // This flavor preserves learned clauses — the solve-1 theory lemmas are
    // re-added at NEW offsets, exactly the "even preserved learned clauses
    // get new indices" case in the #inc-rebuild-reasons mitigation comment.
    solver.cold.l0_gc_modified_clause_db = true;
    assert!(
        !solver.can_use_incremental_reset(),
        "forced rebuild condition must route round 2 through the full reset"
    );

    // Round 2: same solver, same extension — the gate direction.
    let r2 = solver.solve_with_extension(&mut ext).into_inner();
    let SatResult::Sat(m2) = r2 else {
        panic!("round 2 (ext restart across L0-GC arena rebuild) must be SAT, got {r2:?}");
    };
    assert_uflia_sat_model(&m2, "round 2");
    assert!(
        !solver.cold.l0_gc_modified_clause_db,
        "rebuild evidence: the flag is cleared ONLY inside the rebuild branch \
         (preprocess_reset.rs:559) — it must be consumed by round 2's reset"
    );
    assert_level0_arena_reason_facts(&solver, "round 2");

    // Force the DESTRUCTIVE rebuild condition (BVE/BCE/congruence analog).
    // This flavor drops learned clauses: the lemma chain must be re-derived
    // by the extension on the rebuilt arena.
    solver.cold.inprocessing_modified_clause_db = true;
    assert!(
        !solver.can_use_incremental_reset(),
        "forced destructive rebuild condition must route round 3 through the full reset"
    );

    // Round 3: ext restart across the destructive rebuild.
    let r3 = solver.solve_with_extension(&mut ext).into_inner();
    let SatResult::Sat(m3) = r3 else {
        panic!("round 3 (ext restart across destructive arena rebuild) must be SAT, got {r3:?}");
    };
    assert_uflia_sat_model(&m3, "round 3");
    assert!(
        !solver.cold.inprocessing_modified_clause_db,
        "rebuild evidence: destructive flag must be consumed by round 3's reset \
         (preprocess_reset.rs:558)"
    );
}

/// Verdict-soundness direction of the gate: after the rebuild, a new original
/// clause asserting the LIA atom (f(a)<f(c)) must flip the verdict to UNSAT —
/// the post-rebuild extension round must re-derive the lemma chain on the new
/// arena and refute it. Guards against the rebuild silently dropping theory
/// reasoning (a wrong-SAT/wrong-UNSAT vector, not just a panic vector).
#[test]
fn inc5_gate_ext_to_ext_rebuild_with_new_clause_is_sound_unsat() {
    let mut solver = Solver::new(NUM_VARS);
    add_uflia_originals(&mut solver);
    let mut ext = UfliaChainExt::new();

    let r1 = solver.solve_with_extension(&mut ext).into_inner();
    let SatResult::Sat(m1) = r1 else {
        panic!("solve 1 must be SAT, got {r1:?}");
    };
    assert_uflia_sat_model(&m1, "solve 1");
    assert_level0_arena_reason_facts(&solver, "solve 1");

    // Between solves: force the rebuild AND append a new original that
    // contradicts the theory (ledger case (a)+append handled by the rebuild
    // loop re-adding the full ledger).
    solver.cold.l0_gc_modified_clause_db = true;
    assert!(solver.add_clause(vec![pos(LT_FAFC)]));

    let r2 = solver.solve_with_extension(&mut ext).into_inner();
    assert!(
        r2.is_unsat(),
        "solve 2: unit (f(a)<f(c)) against the re-derived lemma chain must be UNSAT, got {r2:?}"
    );
    assert!(
        !solver.cold.l0_gc_modified_clause_db,
        "rebuild evidence: flag must be consumed by solve 2's reset"
    );
}

/// Reverse-order variant: ext solve arms the hazard, then a PLAIN solve
/// re-enters `reset_search_state` across the rebuild. The plain entry must
/// not deref the stale extension-lemma reasons left by solve 1.
#[test]
fn inc5_gate_ext_to_plain_restart_survives_arena_rebuild() {
    let mut solver = Solver::new(NUM_VARS);
    add_uflia_originals(&mut solver);
    let mut ext = UfliaChainExt::new();

    let r1 = solver.solve_with_extension(&mut ext).into_inner();
    let SatResult::Sat(m1) = r1 else {
        panic!("ext solve must be SAT, got {r1:?}");
    };
    assert_uflia_sat_model(&m1, "ext solve");
    assert_level0_arena_reason_facts(&solver, "ext solve");

    solver.cold.l0_gc_modified_clause_db = true;
    assert!(
        !solver.can_use_incremental_reset(),
        "forced rebuild condition must route the plain solve through the full reset"
    );

    let r2 = solver.solve().into_inner();
    let SatResult::Sat(m2) = r2 else {
        panic!("plain solve after ext solve + rebuild must be SAT, got {r2:?}");
    };
    // Plain solve has no extension; assert only ledger-implied facts.
    assert!(m2[EQ_AB as usize] && m2[EQ_BC as usize], "unit originals");
    assert!(m2[FREE_B as usize], "x6 forced by free-var clauses");
    assert!(
        !solver.cold.l0_gc_modified_clause_db,
        "rebuild evidence: flag must be consumed by the plain solve's reset"
    );
}

/// Historically-observed direction (lazy plain solve → eager ext solve): the
/// plain solve leaves its full trail/reason state, the rebuild condition is
/// forced, and the extension solve re-enters the same solver.
#[test]
fn inc5_gate_plain_to_ext_restart_survives_arena_rebuild() {
    let mut solver = Solver::new(NUM_VARS);
    add_uflia_originals(&mut solver);

    let r1 = solver.solve().into_inner();
    assert!(r1.is_sat(), "plain solve must be SAT, got {r1:?}");

    solver.cold.inprocessing_modified_clause_db = true;
    assert!(
        !solver.can_use_incremental_reset(),
        "forced destructive rebuild condition must route the ext solve through the full reset"
    );

    let mut ext = UfliaChainExt::new();
    let r2 = solver.solve_with_extension(&mut ext).into_inner();
    let SatResult::Sat(m2) = r2 else {
        panic!("ext solve after plain solve + destructive rebuild must be SAT, got {r2:?}");
    };
    assert_uflia_sat_model(&m2, "ext solve");
    assert!(
        !solver.cold.inprocessing_modified_clause_db,
        "rebuild evidence: flag must be consumed by the ext solve's reset"
    );
}

/// Regression guard for the historical panic mechanism itself (commit
/// 1ceec34cb9): a `pending_theory_conflict` ClauseRef surviving into the next
/// solve is dereferenced against the rebuilt arena by the CDCL loop's
/// take-site (observed: arena len 6, index ~174M). `reset_search_state` must
/// drop it at solve entry (preprocess_reset.rs:380 #inc-pending-conflict).
///
/// The take-sites also carry a #8480 staleness validation, but that only
/// rescues refs that are still IN bounds of the rebuilt arena — the incident
/// shape is an offset far BEYOND the rebuilt arena's length. To reproduce it
/// at test scale, solve 1 emits 64 padding lemma copies (inflating its arena)
/// and the planted ref is the topmost solve-1 learned-clause offset; the
/// destructive rebuild drops all learned clauses, so the offset is genuinely
/// out of bounds at solve-2's take-site. Mutation-verified: commenting out the
/// `pending_theory_conflict = None` clear in `reset_search_state` makes this
/// test panic with an arena out-of-bounds deref.
#[test]
fn inc5_gate_stale_pending_theory_conflict_cleared_across_rebuild() {
    let mut solver = Solver::new(NUM_VARS);
    add_uflia_originals(&mut solver);
    let mut ext = UfliaChainExt::new();
    ext.padding = 64;

    let r1 = solver.solve_with_extension(&mut ext).into_inner();
    let SatResult::Sat(m1) = r1 else {
        panic!("solve 1 must be SAT, got {r1:?}");
    };
    assert_uflia_sat_model(&m1, "solve 1");
    assert_level0_arena_reason_facts(&solver, "solve 1");

    // Topmost live learned-clause offset from solve 1's (padded) arena — a
    // genuine ClauseRef exactly as #6262's level>0 all-false detection would
    // have stored, far beyond where the destructive rebuild's arena ends.
    let top_learned = solver
        .arena
        .live_indices()
        .filter(|&idx| solver.arena.is_learned(idx))
        .max()
        .expect("solve 1 must have produced theory lemma clauses");
    let top_original = solver
        .arena
        .live_indices()
        .filter(|&idx| !solver.arena.is_learned(idx))
        .max()
        .expect("originals present");
    assert!(
        top_learned > top_original + 64,
        "padding must place the stale ref far beyond the rebuilt-originals \
         region (top_learned={top_learned}, top_original={top_original})"
    );

    // Plant the stale ref, then force the arena rebuild it must not survive.
    solver.pending_theory_conflict = Some(ClauseRef(top_learned as u32));
    solver.cold.inprocessing_modified_clause_db = true;

    // Solve 2 must not re-emit the padding (keeps the rebuilt arena small at
    // the pending-conflict take-site, preserving the out-of-bounds shape).
    ext.padding = 0;
    let r2 = solver.solve_with_extension(&mut ext).into_inner();
    let SatResult::Sat(m2) = r2 else {
        panic!(
            "solve 2 with stale pending_theory_conflict across a rebuild must \
             be SAT (the ref must be dropped at solve entry), got {r2:?}"
        );
    };
    assert_uflia_sat_model(&m2, "solve 2");
    assert!(
        solver.pending_theory_conflict.is_none(),
        "stale pending_theory_conflict must not survive the solve"
    );
}
