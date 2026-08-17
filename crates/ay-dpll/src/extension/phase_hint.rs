// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TermId, TheorySolver};
use ay_sat::{ExtPropagateResult, Extension, SolverContext};
use ay_sat::{Literal, Variable};
use std::cell::Cell;

/// Lightweight extension that only provides phase hints from a theory solver.
///
/// Used by `DpllT::solve_step()` (lazy theory checking mode) to pass theory
/// phase suggestions to the SAT solver without the overhead of eager theory
/// propagation. The split-loop pipeline handles theory checking externally;
/// this extension only provides `suggest_phase` guidance.
///
/// # Motivation (#6282)
///
/// AY's SAT solver defaults to positive phase (true) for uninitialized variables.
/// For array index equality atoms `(= i j)`, this means "assume equal" — the
/// opposite of Z3's default (`m_phase_default = false` → "assume distinct").
/// This causes exponential blowup on storeinv benchmarks because the SAT solver
/// eagerly satisfies index equalities, triggering a cascade of ROW axioms.
///
/// The `PhaseHintExtension` bridges the gap: combined theory solvers (AUFLIA,
/// AUFLRA, etc.) implement `suggest_phase` to return `false` for simple index
/// equality atoms, matching Z3's behavior. This extension forwards those hints
/// to the SAT solver during lazy theory checking.
pub(crate) struct PhaseHintExtension<'a, T: TheorySolver> {
    /// The theory solver (borrowed immutably for suggest_phase)
    theory: &'a T,
    /// Mapping from SAT variables to term IDs
    var_to_term: &'a HashMap<u32, TermId>,
    /// Mapping from term IDs to SAT variables (for suggest_decision)
    term_to_var: &'a HashMap<TermId, u32>,
    /// Theory atoms in registration order (for suggest_decision)
    theory_atoms: &'a [TermId],
    /// Dense, precomputed `(sat_var, atom)` index built once at construction.
    ///
    /// `seed_theory_phases` re-seeds phase hints after EVERY BCP/theory-prop
    /// quiescence, i.e. many times per solve round. The previous implementation
    /// did a `term_to_var.get(atom)` HashMap lookup for every theory atom on
    /// every seed — O(decision_cycles * atoms) hashing that dominated runtime
    /// on LRA/induction benchmarks (profiling: phase-seeding ~20x simplex).
    ///
    /// This pairs each theory atom with its SAT variable id ONCE, so each seed
    /// is a flat slice walk with no per-atom hashing. Atoms with no SAT var
    /// (not registered as a Boolean) are dropped — they contributed nothing to
    /// seeding before either (`term_to_var.get` returned `None`).
    seed_index: Vec<(u32, TermId)>,
    /// Last theory phase-hint epoch this extension seeded at, if the theory
    /// reports one (`TheorySolver::phase_hint_epoch`). When the theory's epoch
    /// is unchanged since the last seed, the suggestions are identical and the
    /// O(atoms) re-seed is skipped entirely. `None` means "not yet seeded this
    /// extension" (seed unconditionally) or "theory does not support epochs"
    /// (also seed unconditionally). Uses `Cell` for interior mutability since
    /// `seed_phase_hints_dual` takes `&self`.
    last_seed_epoch: Cell<Option<u64>>,
    /// Scan index for theory-aware branching (amortized O(1) per call).
    /// Uses Cell for interior mutability since suggest_decision takes &self.
    theory_decision_idx: Cell<usize>,
    /// #8008: Counter for fractional theory-aware branching.
    theory_decision_call_count: Cell<u64>,
}

/// Restores the pre-epoch-skip phase seeding (`AY_DISABLE_PHASE_EPOCH_SKIP`).
///
/// # Why an arm that was deleted is being put back
///
/// The two epoch-skip sites carried the note *"Former `AY_DISABLE_PHASE_EPOCH_SKIP`
/// A/B fallback removed; the skip is permanent."* Removing the arm removes the
/// ability to re-derive the result that justified the skip, and this repo's stated
/// rule is the opposite — `knobs.rs`:
///
/// > the negative results are only RE-CHECKABLE while their arms still exist.
/// > Losing the ability to re-derive a negative result is how a project pays twice
/// > for the same work.
///
/// The skip is almost certainly right: an unchanged epoch means every
/// `suggest_phase(atom)` returns what it returned last time, so the re-seed is
/// provably redundant, and phase hints bias branch order rather than the verdict.
/// That is an argument for the DEFAULT, not for deleting the control. A skip whose
/// premise is "the epoch is a sound cache key" is exactly the kind of claim that
/// stops holding when a theory changes what its epoch counts, and without an arm
/// there is no cheap way to find out.
///
/// Default OFF, so this is behaviour-identical; setting it restores the
/// unconditional O(atoms) re-seed byte-for-byte.
pub(crate) fn phase_epoch_skip_disabled() -> bool {
    // B17: CLI-populated global (--disable-phase-epoch-skip) replaced the
    // never-set env var.
    ay_core::theory_disable_flags().disable_phase_epoch_skip
}

impl<'a, T: TheorySolver> PhaseHintExtension<'a, T> {
    pub(crate) fn new(
        theory: &'a T,
        var_to_term: &'a HashMap<u32, TermId>,
        term_to_var: &'a HashMap<TermId, u32>,
        theory_atoms: &'a [TermId],
    ) -> Self {
        // Build the dense (sat_var, atom) seed index once. This is the same
        // `term_to_var.get(atom)` lookup the seeding loop used to do per atom
        // per seed, hoisted to a single pass at construction. Preserving
        // `theory_atoms` order keeps the seed write order identical to before.
        let mut seed_index = Vec::with_capacity(theory_atoms.len());
        for &atom in theory_atoms {
            if let Some(&sat_var_id) = term_to_var.get(&atom) {
                seed_index.push((sat_var_id, atom));
            }
        }
        Self {
            theory,
            var_to_term,
            term_to_var,
            theory_atoms,
            seed_index,
            last_seed_epoch: Cell::new(None),
            theory_decision_idx: Cell::new(0),
            theory_decision_call_count: Cell::new(0),
        }
    }
}

impl<T: TheorySolver> Extension for PhaseHintExtension<'_, T> {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        // No theory propagation — handled by the split-loop pipeline externally.
        ExtPropagateResult::none()
    }

    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        // Never propagate — avoids redundant propagate() calls in the CDCL loop.
        false
    }

    fn backtrack(&mut self, _new_level: u32) {
        // Reset theory-aware branching scan index on backtrack.
        // Previously decided theory atoms may have been unassigned, so we
        // must re-scan from the start to find unassigned ones.
        // Matches TheoryExtension::backtrack behavior (line 1184).
        self.theory_decision_idx.set(0);
        self.theory_decision_call_count.set(0);
    }

    fn suggest_decision(&self, ctx: &dyn SolverContext) -> Option<Literal> {
        // Theory-aware branching (#6282): decide theory atoms before Tseitin
        // encoding variables. This matches Z3's theory_aware_branching (see
        // smt_case_split_queue.cpp:1170-1209) and ensures the SAT solver
        // assigns all meaningful atoms before auxiliary Tseitin variables.
        //
        // Only enable for theories that support it.
        if !self.theory.supports_theory_aware_branching() {
            return None;
        }
        // #9505: Adaptive theory decision frequency (mirrors TheoryExtension).
        // When decisions/conflicts > 10, use 1-in-1 to give the theory maximum
        // control on BMC/induction-style formulas. See mod.rs for full rationale.
        let count = self.theory_decision_call_count.get();
        self.theory_decision_call_count.set(count + 1);
        let decisions = ctx.decisions();
        let conflicts = ctx.conflicts();
        let theory_every_decision = decisions > 100
            && decisions
                .checked_div(conflicts)
                .is_none_or(|ratio| ratio > 10);
        if !theory_every_decision && !count.is_multiple_of(2) {
            return None;
        }
        // #8445: clauseSMT arithmetic propagation branching. If the theory
        // has a high-priority atom to decide (blocked/fixed variable from
        // feasible-set analysis), decide it immediately.
        if let Some((atom, phase)) = self.theory.suggest_decision_atom() {
            if let Some(&sat_var) = self.term_to_var.get(&atom) {
                let var = Variable::new(sat_var);
                if ctx.value(var).is_none() {
                    let lit = if phase {
                        Literal::positive(var)
                    } else {
                        Literal::negative(var)
                    };
                    return Some(lit);
                }
            }
        }
        // Only decide atoms where the theory has an explicit preference (#6303).
        // Atoms with None phase are left to VSIDS, matching Z3's behavior.
        let start = self.theory_decision_idx.get();
        for (i, &atom) in self.theory_atoms.iter().enumerate().skip(start) {
            if let Some(&sat_var) = self.term_to_var.get(&atom) {
                let var = Variable::new(sat_var);
                if ctx.value(var).is_none() {
                    if let Some(phase) = self.theory.suggest_phase(atom) {
                        self.theory_decision_idx.set(i + 1);
                        let lit = if phase {
                            Literal::positive(var)
                        } else {
                            Literal::negative(var)
                        };
                        return Some(lit);
                    }
                }
            }
        }
        self.theory_decision_idx.set(self.theory_atoms.len());
        None
    }

    fn suggest_phase(&self, var: Variable) -> Option<bool> {
        let term = self.var_to_term.get(&var.id())?;
        self.theory.suggest_phase(*term)
    }

    fn seed_phase_hints(&self, phases: &mut [i8], vals: &[i8]) {
        if !self.theory.supports_theory_aware_branching() {
            return;
        }
        // Walk the precomputed dense (sat_var, atom) index — no per-atom
        // term_to_var hashing. Bit-identical to the previous per-atom loop:
        // atoms with no SAT var were skipped there and are simply absent here.
        for &(sat_var_id, atom) in &self.seed_index {
            let idx = sat_var_id as usize;
            if idx >= phases.len() {
                continue;
            }
            let val_idx = idx * 2;
            if val_idx < vals.len() && vals[val_idx] != 0 {
                continue;
            }
            if let Some(phase) = self.theory.suggest_phase(atom) {
                phases[idx] = if phase { 1 } else { -1 };
            }
        }
    }

    fn seed_phase_hints_dual(&self, phase: &mut [i8], target_phase: &mut [i8], vals: &[i8]) {
        if !self.theory.supports_theory_aware_branching() {
            return;
        }
        // Epoch-skip: when the theory reports a phase-hint epoch and it is
        // unchanged since our last seed, every `suggest_phase(atom)` returns the
        // same value it did last time, so a re-seed would write identical values
        // for the atoms it touches. Skip the whole O(atoms) scan. Phase hints
        // are a heuristic (they bias branch order, never the sat/unsat result),
        // so even where a phase array was overwritten by phase-saving between
        // seeds, leaving it as-is only changes search order, not correctness.
        // The A/B arm is `AY_DISABLE_PHASE_EPOCH_SKIP` (see
        // `phase_epoch_skip_disabled`): default off, and setting it restores the
        // unconditional re-seed byte-for-byte.
        if !phase_epoch_skip_disabled() {
            if let Some(epoch) = self.theory.phase_hint_epoch() {
                if self.last_seed_epoch.get() == Some(epoch) {
                    return;
                }
                self.last_seed_epoch.set(Some(epoch));
            }
        }
        // Single pass over the dense index, writing BOTH arrays with one
        // suggest_phase query per atom. Equivalent to calling seed_phase_hints
        // twice (once per array) but halves the suggest_phase calls and the
        // index walks. The per-array bounds/assignment filtering matches the
        // single-array path exactly, so the two arrays receive the same values
        // the two-scan version produced.
        for &(sat_var_id, atom) in &self.seed_index {
            let idx = sat_var_id as usize;
            let val_idx = idx * 2;
            let assigned = val_idx < vals.len() && vals[val_idx] != 0;
            if assigned {
                continue;
            }
            // Only query the theory once both arrays could potentially be
            // written (i.e. at least one is in bounds for this idx).
            let in_phase = idx < phase.len();
            let in_target = idx < target_phase.len();
            if !in_phase && !in_target {
                continue;
            }
            if let Some(p) = self.theory.suggest_phase(atom) {
                let v = if p { 1 } else { -1 };
                if in_phase {
                    phase[idx] = v;
                }
                if in_target {
                    target_phase[idx] = v;
                }
            }
        }
    }
}
