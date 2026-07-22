// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ProofOutput;

// ========================================================================
// Irredundant Vivification Tests
// ========================================================================

/// Test that vivify_irredundant strengthens an original (non-learned) clause
/// by removing literals that are false at level 0.
///
/// Setup: unit clauses force b=false and c=false at level 0.
/// Original clause (a ∨ b ∨ c) should be strengthened to (a).
/// Since a is the only remaining literal, it becomes a unit and is propagated.
#[test]
fn test_vivify_irredundant_strengthens_original_clause() {
    let mut solver: Solver = Solver::new(3);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    // Unit clauses: force b=false, c=false at level 0
    solver.add_clause(vec![Literal::negative(Variable(1))]);
    solver.add_clause(vec![Literal::negative(Variable(2))]);

    // Original (irredundant) clause: (a ∨ b ∨ c)
    solver.add_clause(vec![a, b, c]);

    // Process initial clauses (propagates units at level 0)
    assert!(solver.process_initial_clauses().is_none());

    // b and c should now be false at level 0
    assert_eq!(solver.lit_value(Literal::negative(Variable(1))), Some(true));
    assert_eq!(solver.lit_value(Literal::negative(Variable(2))), Some(true));

    solver.set_vivify_enabled(true);

    // Run irredundant vivification — should not return conflict
    assert!(!solver.vivify_irredundant());

    // After vivification, a should be propagated (unit from strengthened clause)
    assert_eq!(
        solver.value(Variable(0)),
        Some(true),
        "a should be true after irredundant vivification strengthens (a ∨ b ∨ c) to (a)"
    );
}

/// Test that vivify_irredundant deletes an irredundant clause that is
/// satisfied at level 0 — this is safe because the clause is redundant
/// in the reduced formula (all its satisfying assignments are already forced).
#[test]
fn test_vivify_irredundant_deletes_satisfied_clause() {
    let mut solver: Solver = Solver::new(4);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    // Unit clause: force a=true at level 0
    solver.add_clause(vec![a]);

    // Original clause: (a ∨ b ∨ c) — already satisfied by a=true at level 0
    // This clause SHOULD be deleted (satisfied at level 0 is safe to delete)
    let clause_idx = {
        let idx = solver.arena.len();
        solver.add_clause(vec![a, b, c]);
        idx
    };

    assert!(solver.process_initial_clauses().is_none());

    solver.set_vivify_enabled(true);
    solver.vivify_irredundant();

    // The clause should be deleted (satisfied at level 0)
    assert!(
        solver.arena.is_empty_clause(clause_idx),
        "clause satisfied at level 0 should be deleted by irredundant vivification"
    );
}

/// Test that vivification of an irredundant clause at non-level-0 correctly
/// captures LRAT hint chains from the probe propagation reasons.
///
/// Scenario: target clause (a v b v c). Probing ~a forces b=false via clause 1.
/// Then probing ~c causes a conflict via clauses 2 and 3 (b v c v d) and
/// (b v c v ~d). The strengthened clause should be (a v c) with LRAT hints
/// referencing the reason clause.
///
/// Clause setup ensures nocc scoring orders literals as a > b > c so that
/// vivification probes ~a first, then skips b (already false), then probes ~c.
#[test]
fn test_vivify_non_level0_strengthening_preserves_lrat_reason_hints() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 9);
    let mut solver: Solver = Solver::with_proof_output(9, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));
    let g = Literal::positive(Variable(6));
    let h = Literal::positive(Variable(7));
    let i = Literal::positive(Variable(8));

    // Target clause for vivification (off 0): (a v b v c)
    let c0_off = solver.arena.len();
    solver.add_clause(vec![a, b, c]);
    // Probe reason chain (off c1_off): decide !a => implies !b (b=false).
    let c1_off = solver.arena.len();
    solver.add_clause(vec![a, b.negated()]);
    // Conflict pair: under b=false, c=false these force d and ~d.
    solver.add_clause(vec![b, c, d]);
    solver.add_clause(vec![b, c, d.negated()]);
    // Score boosters for deterministic literal ordering: a > b > c.
    solver.add_clause(vec![a, e, f]);
    solver.add_clause(vec![a, g, h]);
    solver.add_clause(vec![b, e, i]);

    assert!(solver.process_initial_clauses().is_none());
    solver.initialize_watches();
    solver.set_vivify_enabled(true);

    let old_target_id = solver.clause_id(ClauseRef(c0_off as u32));
    let reason_clause_id = solver.clause_id(ClauseRef(c1_off as u32));
    assert_ne!(
        old_target_id, 0,
        "target clause must have an LRAT clause ID"
    );
    assert_ne!(
        reason_clause_id, 0,
        "reason clause must have an LRAT clause ID"
    );

    assert!(
        !solver.vivify_irredundant(),
        "vivify should not derive UNSAT"
    );

    let strengthened = solver.arena.literals(c0_off).to_vec();
    assert_eq!(
        strengthened.len(),
        2,
        "vivify should remove one propagated literal from target clause"
    );
    assert!(
        strengthened.contains(&a) && strengthened.contains(&c) && !strengthened.contains(&b),
        "expected target clause to strengthen from (a v b v c) to (a v c), got {strengthened:?}"
    );

    let new_target_id = solver.clause_id(ClauseRef(c0_off as u32));
    assert_ne!(
        new_target_id, old_target_id,
        "replacement must resync clause ID after LRAT add-before-delete"
    );

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let replacement_line = proof_text
        .lines()
        .find(|line| line.starts_with(&format!("{new_target_id} ")))
        .expect("expected replacement LRAT addition line");

    let tokens: Vec<&str> = replacement_line.split_whitespace().collect();
    let lit_terminator = tokens
        .iter()
        .position(|&token| token == "0")
        .expect("LRAT line must contain literal terminator");
    let hints: Vec<u64> = tokens[lit_terminator + 1..]
        .iter()
        .take_while(|&&token| token != "0")
        .map(|token| token.parse::<u64>().expect("hint must parse as u64"))
        .collect();

    assert!(
        hints.contains(&reason_clause_id),
        "replacement hints must include captured probe reason clause ID; got {hints:?}"
    );
    assert!(
        hints.contains(&old_target_id),
        "replacement hints must include original clause ID; got {hints:?}"
    );
    assert!(
        hints.len() >= 2,
        "replacement hints must include at least reason + original clause IDs; got {hints:?}"
    );
}

/// Regression test: vivify's collect_vivify_probe_lrat_hints must include
/// level0_proof_id for ClearLevel0 victims in the LRAT hint chain (#5014).
///
/// This tests the vivify.rs ClearLevel0 code path (lines 664, 713, 750, 765),
/// which is separate from the replace_clause_impl path tested in mutate.rs's
/// test_replace_clause_checked_level0_proof_id_fallback_after_clearlevel0.
///
/// Scenario:
/// 1. BVE deletes unit clause c1=(¬x2) via ClearLevel0, clearing reason[2]
///    but preserving c1's LRAT ID in level0_proof_id[2].
/// 2. Vivification probes c0=(x0 ∨ x1 ∨ x3):
///    - Decide ¬x0 → c2=(x0 ∨ x2 ∨ ¬x1) propagates x1=false
///    - Skip x1 (already false via propagation)
///    - Decide ¬x3 → c_force=(x3 ∨ ¬x5) propagates x5=false
///    - c3=(x1 ∨ x2 ∨ x5) conflict (all false: x1 from step 2, x2 at L0, x5 from step 3)
/// 3. c3 contains x2 at level 0. reason[2]=None but level0_proof_id[2]=c1_id,
///    so the LRAT hint chain must include c1_id.
/// 4. c3's non-L0 lits are {x1, x5}. x5 ∉ c0, so c3 does NOT subsume c0 →
///    vivify strengthens c0 to (x0 ∨ x3) rather than deleting it.
#[test]
fn test_vivify_probe_lrat_hints_include_level0_proof_id_after_clearlevel0() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 10);
    let mut solver: Solver = Solver::with_proof_output(6, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let x3 = Literal::positive(Variable(3));
    let x4 = Literal::positive(Variable(4));
    let x5 = Literal::positive(Variable(5));

    // c0: target clause for vivification
    let c0_off = solver.arena.len();
    solver.add_clause(vec![x0, x1, x3]);
    // c1: unit clause, propagates x2=false at level 0
    let c1_off = solver.arena.len();
    solver.add_clause(vec![x2.negated()]);
    // c2: under x0=false + x2=false → unit ¬x1, propagates x1=false
    solver.add_clause(vec![x0, x2, x1.negated()]);
    // c_force: under x3=false → propagates x5=false
    solver.add_clause(vec![x3, x5.negated()]);
    // c3: under x1=false + x2=false + x5=false → conflict (all false)
    // Non-L0 lits {x1, x5} — x5 ∉ c0, so c3 does NOT subsume c0.
    solver.add_clause(vec![x1, x2, x5]);
    // Score boosters: ensure nocc order x0+ > x1+ > x3+ for deterministic
    // vivification literal ordering. All contain ¬x2 (true at L0) so they
    // are satisfied at level 0 and don't interfere with the probe.
    solver.add_clause(vec![x0, x4.negated(), x2.negated()]); // boost x0+
    solver.add_clause(vec![x1, x4.negated(), x2.negated()]); // boost x1+
    solver.add_clause(vec![x0, x2.negated(), x4]); // boost x0+ again

    assert!(solver.process_initial_clauses().is_none());

    // Verify x2=false at level 0 from c1 unit propagation
    assert!(
        solver.lit_val(x2) < 0,
        "x2 should be false at level 0 after unit propagation of c1"
    );

    // Save c1's clause ID, then simulate ClearLevel0: BVE deletes c1,
    // clearing reason[2] but preserving the LRAT clause ID.
    let c1_id = solver.clause_id(ClauseRef(c1_off as u32));
    assert_ne!(c1_id, 0, "c1 must have a non-zero LRAT ID");
    solver.var_data[2].reason = NO_REASON;
    solver.record_level0_proof_id_for_lit(x2.negated(), c1_id);

    // Advance qhead past initial unit propagation (simulates completed L0 BCP)
    solver.qhead = solver.trail.len();

    solver.initialize_watches();
    solver.set_vivify_enabled(true);

    let old_c0_id = solver.clause_id(ClauseRef(c0_off as u32));
    assert_ne!(old_c0_id, 0, "c0 must have a non-zero LRAT ID");

    assert!(
        !solver.vivify_irredundant(),
        "vivify should not derive UNSAT"
    );

    // Verify c0 was strengthened (x1 removed as propagated-false literal)
    let new_lits = solver.arena.literals(c0_off).to_vec();
    assert!(
        new_lits.len() < 3,
        "vivify should strengthen c0 from 3 literals, got {new_lits:?}"
    );

    // Get c0's new clause ID after replacement
    let new_c0_id = solver.clause_id(ClauseRef(c0_off as u32));
    assert_ne!(
        new_c0_id, old_c0_id,
        "replacement must assign new clause ID"
    );

    // Parse LRAT proof and find c0's replacement addition line
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");

    let replacement_line = proof_text
        .lines()
        .find(|line| line.starts_with(&format!("{new_c0_id} ")))
        .unwrap_or_else(|| {
            panic!(
                "expected LRAT addition line for c0 replacement ID {new_c0_id}\n\
                 Full LRAT:\n{proof_text}"
            )
        });

    let tokens: Vec<&str> = replacement_line.split_whitespace().collect();
    let lit_terminator = tokens
        .iter()
        .position(|&t| t == "0")
        .expect("LRAT line must contain literal terminator");
    let hints: Vec<u64> = tokens[lit_terminator + 1..]
        .iter()
        .take_while(|&&t| t != "0")
        .map(|t| t.parse::<u64>().expect("hint must parse as u64"))
        .collect();

    assert!(
        hints.contains(&c1_id),
        "c0 replacement LRAT hints must include c1's ID ({c1_id}) via \
         level0_proof_id fallback in collect_vivify_probe_lrat_hints \
         (ClearLevel0 cleared reason[2] but saved proof ID). \
         Got hints: {hints:?}\nFull LRAT:\n{proof_text}"
    );
}

#[test]
fn test_vivify_simplifies_learned_clause_and_propagates_unit() {
    let mut solver = Solver::new(3);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    solver.add_clause(vec![Literal::negative(Variable(1))]);
    solver.add_clause(vec![Literal::negative(Variable(2))]);

    let learned = solver.add_learned_clause(vec![a, b, c], 3, &[]);

    assert!(solver.process_initial_clauses().is_none());
    solver.set_vivify_enabled(true);
    // Ensure the learned tier is due for vivification.
    solver.num_conflicts = solver.inproc_ctrl.vivify.next_conflict;

    assert!(!solver.vivify());

    let learned_idx = learned.0 as usize;
    assert_eq!(solver.arena.len_of(learned_idx), 1);
    assert_eq!(solver.arena.literal(learned_idx, 0), a);

    assert_eq!(solver.value(Variable(0)), Some(true));
    assert_eq!(solver.value(Variable(1)), Some(false));
    assert_eq!(solver.value(Variable(2)), Some(false));
}

#[test]
fn test_vivify_irred_schedule_honors_enabled_flag_and_public_reenable() {
    let mut solver: Solver = Solver::new(3);

    solver.num_conflicts = 10_000;
    solver.inproc_ctrl.vivify.next_conflict = solver.num_conflicts + 1;
    solver.inproc_ctrl.vivify_irred.next_conflict = solver.num_conflicts;

    solver.inproc_ctrl.vivify.enabled = true;
    solver.inproc_ctrl.vivify_irred.enabled = false;

    assert!(!solver.should_vivify_irred());
    assert!(!solver.should_vivify());

    solver.disable_all_inprocessing();
    assert!(!solver.inproc_ctrl.vivify.enabled);
    assert!(!solver.inproc_ctrl.vivify_irred.enabled);

    solver.set_vivify_enabled(true);
    assert!(solver.inproc_ctrl.vivify.enabled);
    assert!(solver.inproc_ctrl.vivify_irred.enabled);
    assert!(solver.should_vivify_irred());
    assert!(solver.should_vivify());
}

#[test]
fn test_vivify_skips_irredundant_tier_when_not_due() {
    let mut solver: Solver = Solver::new(3);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    solver.add_clause(vec![Literal::negative(Variable(1))]);
    solver.add_clause(vec![Literal::negative(Variable(2))]);
    solver.add_clause(vec![a, b, c]);

    assert!(solver.process_initial_clauses().is_none());
    solver.set_vivify_enabled(true);

    // Neither tier is due: both scheduled in the future.
    solver.num_conflicts = 10_000;
    solver.inproc_ctrl.vivify.next_conflict = solver.num_conflicts + 1;
    solver.inproc_ctrl.vivify_irred.next_conflict = solver.num_conflicts + 1;

    assert!(!solver.should_vivify_irred());
    assert!(!solver.should_vivify());
    assert!(!solver.vivify());
    assert_eq!(solver.value(Variable(0)), None);
}

#[test]
fn test_vivify_runs_irredundant_tier_when_due() {
    let mut solver: Solver = Solver::new(3);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    solver.add_clause(vec![Literal::negative(Variable(1))]);
    solver.add_clause(vec![Literal::negative(Variable(2))]);
    solver.add_clause(vec![a, b, c]);

    assert!(solver.process_initial_clauses().is_none());
    solver.set_vivify_enabled(true);

    // Learned tier not due; irredundant tier is due.
    solver.num_conflicts = 10_000;
    solver.inproc_ctrl.vivify.next_conflict = solver.num_conflicts + 1;
    solver.inproc_ctrl.vivify_irred.next_conflict = solver.num_conflicts;

    assert!(solver.should_vivify_irred());
    assert!(solver.should_vivify());
    // Irredundant vivification should strengthen the clause (b,c are false at level 0).
    assert!(!solver.vivify());
    // Variable 0 should be assigned true (unit propagation after strengthening).
    assert_eq!(solver.value(Variable(0)), Some(true));
}

#[test]
fn test_vivify_irred_adaptive_delay_doubles_on_low_yield() {
    let mut solver: Solver = Solver::new(3);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    solver.add_clause(vec![a, b, c]);

    assert!(solver.process_initial_clauses().is_none());
    solver.set_vivify_enabled(true);

    solver.num_conflicts = 5_000;
    solver.cold.vivify_irred_delay_multiplier = 1;

    assert!(!solver.vivify_irredundant());
    assert_eq!(solver.cold.vivify_irred_delay_multiplier, 2);
    assert_eq!(
        solver.inproc_ctrl.vivify_irred.next_conflict,
        solver.num_conflicts + (VIVIFY_IRRED_INTERVAL * 2)
    );
}

#[test]
fn test_vivify_irred_adaptive_delay_resets_on_productive_pass() {
    let mut solver: Solver = Solver::new(3);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    solver.add_clause(vec![Literal::negative(Variable(1))]);
    solver.add_clause(vec![Literal::negative(Variable(2))]);
    solver.add_clause(vec![a, b, c]);

    assert!(solver.process_initial_clauses().is_none());
    solver.set_vivify_enabled(true);

    solver.num_conflicts = 7_500;
    solver.cold.vivify_irred_delay_multiplier = 8;

    assert!(!solver.vivify_irredundant());
    assert_eq!(solver.cold.vivify_irred_delay_multiplier, 1);
    assert_eq!(
        solver.inproc_ctrl.vivify_irred.next_conflict,
        solver.num_conflicts + VIVIFY_IRRED_INTERVAL
    );
}

#[test]
fn test_vivify_irredundant_budgets_level0_satisfied_candidate_scan() {
    let num_candidates = VIVIFY_IRRED_CLAUSES_PER_CALL + 50;
    let mut solver: Solver = Solver::new(1 + num_candidates * 2);

    let a = Literal::positive(Variable(0));
    solver.add_clause(vec![a]);

    for i in 0..num_candidates {
        let b = Literal::positive(Variable((1 + (i * 2)) as u32));
        let c = Literal::positive(Variable((2 + (i * 2)) as u32));
        solver.add_clause(vec![a, b, c]);
    }

    assert!(solver.process_initial_clauses().is_none());
    assert_eq!(solver.value(Variable(0)), Some(true));

    solver.set_vivify_enabled(true);
    assert!(
        !solver.vivify_irredundant(),
        "vivify should not derive UNSAT while deleting level-0 satisfied clauses",
    );

    let stats = solver.vivify_stats();
    assert_eq!(
        stats.clauses_examined, VIVIFY_IRRED_CLAUSES_PER_CALL as u64,
        "irredundant vivify should stop after spending its per-call budget even when \
         candidates are already satisfied and do not consume vivify_ticks",
    );
    assert_eq!(
        stats.clauses_satisfied, VIVIFY_IRRED_CLAUSES_PER_CALL as u64,
        "only budgeted level-0 satisfied candidates should be deleted in one pass",
    );
}

#[test]
fn test_vivify_irredundant_advances_after_level0_deletion() {
    let mut solver: Solver = Solver::new(6);

    let a = Literal::positive(Variable(0));
    let d = Literal::positive(Variable(3));

    solver.add_clause(vec![a]);
    let first_candidate_idx = solver.arena.len();
    solver.add_clause(vec![
        a,
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![d]);
    let second_candidate_idx = solver.arena.len();
    solver.add_clause(vec![
        d,
        Literal::positive(Variable(4)),
        Literal::positive(Variable(5)),
    ]);

    assert!(solver.process_initial_clauses().is_none());
    solver.set_vivify_enabled(true);

    assert!(
        !solver.vivify_irredundant(),
        "vivify should not derive UNSAT while deleting level-0 satisfied clauses",
    );

    let stats = solver.vivify_stats();
    assert_eq!(
        stats.clauses_examined, 2,
        "vivify should advance to the next candidate after deleting a level-0 satisfied clause",
    );
    assert!(
        solver.arena.is_empty_clause(first_candidate_idx),
        "first satisfied candidate should be deleted",
    );
    assert!(
        solver.arena.is_empty_clause(second_candidate_idx),
        "second satisfied candidate should also be reached and deleted in the same pass",
    );
}

#[test]
fn test_vivify_inline_conflict_subsumption_deletes_clause() {
    let mut solver: Solver = Solver::new(4);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));

    let candidate_idx = solver.arena.len();
    solver.add_clause(vec![a, b, c, d]);

    // Binary clauses that force a conflict when vivify probes `!a`:
    //   !a → !b  (from (a v !b))
    //   !a → !d  (from (a v !d))
    //   (b v d) conflicts when both b=false and d=false.
    // All auxiliary clauses are binary (< 3 literals) so they are NOT vivify
    // candidates. Only the 4-literal candidate is probed.
    // Conflict clause (b v d) ⊆ candidate (a v b v c v d) → inline subsumption.
    solver.add_clause(vec![a, b.negated()]);
    solver.add_clause(vec![a, d.negated()]);
    solver.add_clause(vec![b, d]);

    assert!(solver.process_initial_clauses().is_none());
    solver.initialize_watches();
    solver.set_vivify_enabled(true);

    assert!(
        !solver.vivify_irredundant(),
        "vivify should delete the candidate without deriving UNSAT",
    );

    assert!(
        solver.arena.is_empty_clause(candidate_idx),
        "inline conflict-clause subsumption should delete the candidate instead of strengthening it",
    );

    let stats = solver.vivify_stats();
    assert_eq!(
        stats.inline_subsumed, 1,
        "expected one direct conflict-clause subsumption",
    );
    assert_eq!(
        stats.clauses_strengthened, 0,
        "candidate should be deleted, not rewritten to a shorter clause",
    );
    assert_eq!(
        stats.clauses_satisfied, 1,
        "deleting the subsumed clause should count as a satisfied/removable clause",
    );
    assert_eq!(
        solver.value(Variable(0)),
        None,
        "deleting the candidate should not leave a unit assignment behind",
    );
    assert_eq!(
        solver.value(Variable(1)),
        None,
        "deleting the candidate should not leave a unit assignment behind",
    );
}

#[test]
fn test_vivify_inline_conflict_subsumption_promotes_learned_subsumer() {
    let mut solver: Solver = Solver::new(4);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));

    let candidate_idx = solver.arena.len();
    solver.add_clause(vec![a, b, c, d]);

    // Binary implications force b=false and d=false under vivify probe !a.
    solver.add_clause(vec![a, b.negated()]);
    solver.add_clause(vec![a, d.negated()]);

    // Learned binary conflict clause: once b=false and d=false, the conflict
    // clause (b v d) directly subsumes the irredundant candidate. CaDiCaL
    // promotes the learned subsumer before deleting the candidate.
    let learned_subsumer = solver.add_learned_clause(vec![b, d], 2, &[]);
    let learned_idx = learned_subsumer.0 as usize;
    assert!(
        solver.arena.is_learned(learned_idx),
        "test requires a learned subsumer before vivification",
    );

    assert!(solver.process_initial_clauses().is_none());
    solver.initialize_watches();
    solver.set_vivify_enabled(true);

    assert!(
        !solver.vivify_irredundant(),
        "vivify should delete the candidate without deriving UNSAT",
    );

    assert!(
        solver.arena.is_empty_clause(candidate_idx),
        "inline subsumption by a learned conflict clause should still delete the candidate",
    );
    assert!(
        !solver.arena.is_learned(learned_idx),
        "learned conflict clause should be promoted to irredundant before deleting the candidate",
    );

    let stats = solver.vivify_stats();
    assert_eq!(
        stats.inline_subsumed, 1,
        "expected one direct conflict-clause subsumption",
    );
    assert_eq!(
        stats.clauses_satisfied, 1,
        "deleting the subsumed clause should count as a satisfied/removable clause",
    );
}

#[test]
fn test_vivify_implied_literal_backward_analysis_strengthens_clause() {
    let mut solver: Solver = Solver::new(6);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));

    let candidate_idx = solver.arena.len();
    solver.add_clause(vec![a, b, c, d]);

    // Probe !a => e=true => b=true. No single reason clause is a subset of the
    // candidate, so the implied-literal path must keep the necessary decision
    // literal and the implied literal, strengthening to (a v b) instead of
    // deleting the clause.
    solver.add_clause(vec![a, e]);
    solver.add_clause(vec![e.negated(), b]);

    // Score booster so vivify probes !a before it reaches b.
    solver.add_clause(vec![a, f]);

    assert!(solver.process_initial_clauses().is_none());
    solver.initialize_watches();
    solver.set_vivify_enabled(true);

    assert!(
        !solver.vivify_irredundant(),
        "vivify should strengthen the candidate without deriving UNSAT",
    );

    let strengthened = solver.arena.literals(candidate_idx).to_vec();
    assert_eq!(
        strengthened.len(),
        2,
        "implied-literal backward analysis should strengthen the clause to two literals",
    );
    assert!(
        strengthened.contains(&a) && strengthened.contains(&b),
        "expected strengthened clause to keep only the necessary decision literal and the implied literal, got {strengthened:?}",
    );

    let stats = solver.vivify_stats();
    assert_eq!(
        stats.clauses_strengthened, 1,
        "implied-literal backward analysis should strengthen, not delete, the clause",
    );
    assert_eq!(
        stats.analysis_subsumed, 0,
        "no concrete subset reason clause exists in this scenario",
    );
    assert_eq!(
        stats.clauses_satisfied, 0,
        "strengthening should not count as deleting a satisfied clause",
    );
}

#[test]
fn test_vivify_implied_literal_prefers_earliest_true_candidate_on_trail() {
    let mut solver: Solver = Solver::new(9);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));
    let g = Literal::positive(Variable(6));
    let h = Literal::positive(Variable(7));
    let i = Literal::positive(Variable(8));

    let candidate_idx = solver.arena.len();
    solver.add_clause(vec![a, b, c, d]);

    // Probe !a => e=true => c=true => b=true.
    //
    // b is sorted before c thanks to the booster clause below, but c becomes
    // true earlier on the trail. CaDiCaL re-picks that earlier implied
    // literal before backward analysis (`better_subsume_trail`), so the
    // vivified clause should keep c rather than the later b implication.
    solver.add_clause(vec![a, e]);
    solver.add_clause(vec![e.negated(), c]);
    solver.add_clause(vec![c.negated(), b]);
    // Binary boosters contribute to nocc scoring without becoming vivify
    // candidates themselves. Boost a highest so !a is probed first, then
    // keep b ahead of c within the remaining literal order.
    solver.add_clause(vec![a, f]);
    solver.add_clause(vec![a, g]);
    solver.add_clause(vec![b, h]);
    solver.add_clause(vec![b, i]);

    assert!(solver.process_initial_clauses().is_none());
    solver.initialize_watches();
    solver.set_vivify_enabled(true);

    assert!(
        !solver.vivify_irredundant(),
        "vivify should strengthen the candidate without deriving UNSAT",
    );

    let strengthened = solver.arena.literals(candidate_idx).to_vec();
    assert_eq!(
        strengthened.len(),
        2,
        "earliest-implied selection should still strengthen to two literals",
    );
    assert!(
        strengthened.contains(&a) && strengthened.contains(&c),
        "expected vivify to keep the earliest implied candidate literal c, got {strengthened:?}",
    );
    assert!(
        !strengthened.contains(&b),
        "later implied literal b should not be chosen once c appears earlier on the trail; got {strengthened:?}",
    );
}

#[test]
fn test_vivify_implied_literal_lrat_hints_follow_earliest_true_candidate() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(9, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));
    let g = Literal::positive(Variable(6));
    let h = Literal::positive(Variable(7));
    let i = Literal::positive(Variable(8));

    let candidate_idx = solver.arena.len();
    solver.add_clause(vec![a, b, c, d]);
    let a_to_e_off = solver.arena.len();
    solver.add_clause(vec![a, e]);
    let e_to_c_off = solver.arena.len();
    solver.add_clause(vec![e.negated(), c]);
    let c_to_b_off = solver.arena.len();
    solver.add_clause(vec![c.negated(), b]);
    // Binary boosters contribute to nocc scoring without becoming vivify
    // candidates themselves. Boost a highest so !a is probed first, then
    // keep b ahead of c within the remaining literal order.
    solver.add_clause(vec![a, f]);
    solver.add_clause(vec![a, g]);
    solver.add_clause(vec![b, h]);
    solver.add_clause(vec![b, i]);

    assert!(solver.process_initial_clauses().is_none());
    solver.initialize_watches();
    solver.set_vivify_enabled(true);

    let old_candidate_id = solver.clause_id(ClauseRef(candidate_idx as u32));
    let a_to_e_id = solver.clause_id(ClauseRef(a_to_e_off as u32));
    let e_to_c_id = solver.clause_id(ClauseRef(e_to_c_off as u32));
    let c_to_b_id = solver.clause_id(ClauseRef(c_to_b_off as u32));

    assert!(
        !solver.vivify_irredundant(),
        "vivify should strengthen the candidate without deriving UNSAT",
    );

    let strengthened = solver.arena.literals(candidate_idx).to_vec();
    assert!(
        strengthened.contains(&a) && strengthened.contains(&c) && !strengthened.contains(&b),
        "expected LRAT-backed vivify strengthening to keep the earliest implied literal c, got {strengthened:?}",
    );

    let new_candidate_id = solver.clause_id(ClauseRef(candidate_idx as u32));
    assert_ne!(
        new_candidate_id, old_candidate_id,
        "replacement must assign a fresh LRAT clause ID",
    );

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let replacement_line = proof_text
        .lines()
        .find(|line| line.starts_with(&format!("{new_candidate_id} ")))
        .unwrap_or_else(|| {
            panic!(
                "expected LRAT addition line for replacement ID {new_candidate_id}\n\
                 Full LRAT:\n{proof_text}"
            )
        });

    let tokens: Vec<&str> = replacement_line.split_whitespace().collect();
    let lit_terminator = tokens
        .iter()
        .position(|&token| token == "0")
        .expect("LRAT line must contain literal terminator");
    let hints: Vec<u64> = tokens[lit_terminator + 1..]
        .iter()
        .take_while(|&&token| token != "0")
        .map(|token| token.parse::<u64>().expect("hint must parse as u64"))
        .collect();

    assert!(
        hints.contains(&old_candidate_id),
        "replacement hints must include the original clause ID; got {hints:?}",
    );
    assert!(
        hints.contains(&a_to_e_id),
        "replacement hints must include the first reason in the earlier c chain; got {hints:?}",
    );
    assert!(
        hints.contains(&e_to_c_id),
        "replacement hints must include the c-implying reason; got {hints:?}",
    );
    assert!(
        !hints.contains(&c_to_b_id),
        "replacement hints should not justify the later b implication once c is chosen as the implied literal; got {hints:?}",
    );
}

#[test]
fn test_vivify_implied_literal_subsumption_promotes_learned_subsumer() {
    let mut solver: Solver = Solver::new(5);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));

    let candidate_idx = solver.arena.len();
    solver.add_clause(vec![a, b, c, d]);

    // Probe !a makes b=true via the learned binary reason clause (a v b),
    // which is itself a subset of the candidate. The implied-literal analysis
    // should therefore promote the learned subsumer and delete the candidate.
    let learned_subsumer = solver.add_learned_clause(vec![a, b], 2, &[]);
    let learned_idx = learned_subsumer.0 as usize;

    // Score booster so vivify probes !a before it reaches b.
    solver.add_clause(vec![a, e]);

    assert!(solver.process_initial_clauses().is_none());
    solver.initialize_watches();
    solver.set_vivify_enabled(true);

    assert!(
        !solver.vivify_irredundant(),
        "vivify should delete the candidate without deriving UNSAT",
    );

    assert!(
        solver.arena.is_empty_clause(candidate_idx),
        "the implied-literal learned subsumer should delete the candidate",
    );
    assert!(
        !solver.arena.is_learned(learned_idx),
        "the learned implied subsumer should be promoted before deleting the irredundant candidate",
    );

    let stats = solver.vivify_stats();
    assert_eq!(
        stats.analysis_subsumed, 1,
        "expected one implied-literal analysis subsumption",
    );
    assert_eq!(
        stats.clauses_satisfied, 1,
        "deleting the subsumed clause should count as a satisfied/removable clause",
    );
}

/// Test that the vivification instantiation path produces valid LRAT hints.
///
/// The instantiation path (vivify.rs ~line 584-623) triggers when standard
/// probing of all literals causes no conflict, but deciding the LAST sorted
/// literal POSITIVELY causes a conflict. This proves the last literal is
/// redundant and can be removed from the clause.
///
/// Key insight: the conflict from c=true must go through a 2-step propagation
/// chain (c=true → e=false → conflict) to prevent BCP from backward-chaining
/// ¬c during the probing phase. A direct binary conflict (¬c ∨ ¬d) would
/// propagate c=false at L1 when d=true, preventing the instantiation path.
///
/// Scenario:
/// - Target c0: (a v b v c), nocc ordering a > b > c, so c is last.
/// - c1: (a v d)          — ¬a (a=false) propagates d=true at L1
/// - c2: (¬c v ¬d v e)   — conflict clause: c=T, d=T, e=F → all false
/// - c3: (¬c v ¬e)       — c=true propagates e=false (forward chain)
/// - c4: (b v f v g)     — nocc booster for b+ (ensures a > b > c ordering)
///
/// Probing: ¬a (→ d=T, no conflict), ¬b (no conflict), ¬c (c2 and c3
/// satisfied, no conflict). Backtrack one level (undo ¬c), decide c positively:
/// c3 → e=F, then c2 → (F v F v F) → conflict! Instantiation removes c.
///
/// LRAT proof for replacement (a v b): under RUP negation ¬a, ¬b:
///   c0 → c=T, c1 → d=T, c3 → e=F, c2 → conflict.
#[test]
fn test_vivify_instantiation_path_lrat_hints() {
    // 7 variables: a=0, b=1, c=2, d=3, e=4, f=5, g=6
    // 5 original clauses
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 5);
    let mut solver: Solver = Solver::with_proof_output(7, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));
    let g = Literal::positive(Variable(6));

    // c0: target clause (a v b v c), ID 1
    let c0_off = solver.arena.len();
    solver.add_clause(vec![a, b, c]);
    // c1: (a v d), ID 2 — a=false propagates d=true
    let c1_off = solver.arena.len();
    solver.add_clause(vec![a, d]);
    // c2: (¬c v ¬d v e), ID 3 — conflict: c=T, d=T, e=F → all false
    let c2_off = solver.arena.len();
    solver.add_clause(vec![c.negated(), d.negated(), e]);
    // c3: (¬c v ¬e), ID 4 — c=true propagates e=false (forward chain)
    let c3_off = solver.arena.len();
    solver.add_clause(vec![c.negated(), e.negated()]);
    // c4: (b v f v g), ID 5 — nocc booster for b+
    solver.add_clause(vec![b, f, g]);

    assert!(solver.process_initial_clauses().is_none());
    solver.initialize_watches();
    solver.set_vivify_enabled(true);

    let c0_id = solver.clause_id(ClauseRef(c0_off as u32));
    let c1_id = solver.clause_id(ClauseRef(c1_off as u32));
    let c2_id = solver.clause_id(ClauseRef(c2_off as u32));
    let c3_id = solver.clause_id(ClauseRef(c3_off as u32));
    assert_ne!(c0_id, 0, "c0 must have a non-zero LRAT ID");
    assert_ne!(c1_id, 0, "c1 must have a non-zero LRAT ID");
    assert_ne!(c2_id, 0, "c2 must have a non-zero LRAT ID");
    assert_ne!(c3_id, 0, "c3 must have a non-zero LRAT ID");

    assert!(
        !solver.vivify_irredundant(),
        "vivify should not derive UNSAT"
    );

    // Verify c0 was strengthened: c should be removed (instantiation path)
    let new_lits = solver.arena.literals(c0_off).to_vec();
    assert!(
        new_lits.len() < 3,
        "vivify instantiation should remove the last literal (c), got {new_lits:?}"
    );
    assert!(
        new_lits.contains(&a) && new_lits.contains(&b),
        "expected (a v b) after instantiation removes c, got {new_lits:?}"
    );
    assert!(
        !new_lits.contains(&c),
        "c should have been removed by instantiation, got {new_lits:?}"
    );

    // Get replacement clause ID
    let new_c0_id = solver.clause_id(ClauseRef(c0_off as u32));
    assert_ne!(
        new_c0_id, c0_id,
        "replacement must assign new clause ID after LRAT add-before-delete"
    );

    // Parse LRAT proof output
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");

    let replacement_line = proof_text
        .lines()
        .find(|line| line.starts_with(&format!("{new_c0_id} ")))
        .unwrap_or_else(|| {
            panic!(
                "expected LRAT addition line for replacement ID {new_c0_id}\n\
                 Full LRAT:\n{proof_text}"
            )
        });

    let tokens: Vec<&str> = replacement_line.split_whitespace().collect();
    let lit_terminator = tokens
        .iter()
        .position(|&t| t == "0")
        .expect("LRAT line must contain literal terminator");
    let hints: Vec<u64> = tokens[lit_terminator + 1..]
        .iter()
        .take_while(|&&t| t != "0")
        .map(|t| t.parse::<u64>().expect("hint must parse as u64"))
        .collect();

    // Verify LRAT hints contain all four essential clause IDs:
    // c0 (original clause → derives c=T under RUP negation),
    // c1 (a v d → derives d=T),
    // c3 (¬c v ¬e → derives e=F),
    // c2 (¬c v ¬d v e → conflict)
    assert!(
        hints.contains(&c0_id),
        "instantiation LRAT hints must include original clause c0 ID ({c0_id}); \
         got hints: {hints:?}\nFull LRAT:\n{proof_text}"
    );
    assert!(
        hints.contains(&c1_id),
        "instantiation LRAT hints must include propagation reason c1 ID ({c1_id}); \
         got hints: {hints:?}\nFull LRAT:\n{proof_text}"
    );
    assert!(
        hints.contains(&c2_id),
        "instantiation LRAT hints must include conflict clause c2 ID ({c2_id}); \
         got hints: {hints:?}\nFull LRAT:\n{proof_text}"
    );
    assert!(
        hints.contains(&c3_id),
        "instantiation LRAT hints must include chain clause c3 ID ({c3_id}); \
         got hints: {hints:?}\nFull LRAT:\n{proof_text}"
    );
    assert!(
        hints.len() >= 4,
        "instantiation LRAT hints must have at least 4 entries; \
         got {}: {hints:?}",
        hints.len()
    );
}
