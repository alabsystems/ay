// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MIC (Minimal Inductive Clause) generalization for clause-level IC3 (#8211).
//!
//! Given a cube `c` blocked at level `k` (meaning `F_{k-1} /\ T /\ c' => false`,
//! i.e., no predecessor in F_{k-1} can transition to c), generalization
//! attempts to find a smaller sub-cube that is still inductive relative
//! to F_{k-1}.
//!
//! Two phases:
//! 1. **UNSAT core shrink (down)**: Use the UNSAT core from the blocking
//!    query to identify a subset of next-state literals that were needed.
//!    Map these back to current-state literals.
//! 2. **Literal dropping (MIC)**: Try removing each remaining literal one
//!    at a time. If the reduced cube is still inductive, keep the removal.
//!
//! Reference: Bradley VMCAI 2011, Section 4.

use super::cube::Cube;
use super::solver::Ic3Solver;
use ay_sat::{AssumeResult, Literal};

/// Maximum CTG recursion depth (mirrors the reference IC3 implementation `MAX_CTG_RECURSION`).
///
/// The outermost MIC runs at `ctg_depth == 0` with the CTG inner loop
/// enabled; a `trivial_block` recursion bumps `ctg_depth` to 1, which (being
/// `>= MAX_CTG_RECURSION`) disables further CTG nesting. This bounds the
/// recursion to one level, preventing exponential blowup.
const MAX_CTG_RECURSION: usize = 1;

/// Maximum number of CTG attempts per failed literal drop (the reference implementation's `ctg_max`).
const CTG_MAX: usize = 3;

/// `trivial_block` predecessor-blocking budget per CTG attempt (the reference implementation's `ctg_limit`).
const CTG_LIMIT: usize = 1;

/// Independent-consecution cross-check threshold (the reference implementation's
/// `VERIFY_CONSECUTION_INDEPENDENT_MAX_LATCHES`). For transition systems with
/// at most this many state variables, EVERY generalized cube is re-verified on
/// a fresh, independent `ay_sat::Solver` (default mode, full BCP) to catch a
/// false-UNSAT from the IC3-tuned incremental solver that could otherwise let
/// MIC drop an essential literal and produce an unsound lemma.
const VERIFY_CONSECUTION_INDEPENDENT_MAX_STATE_VARS: usize = 60;

impl Ic3Solver {
    /// Generalize a blocked cube using MIC (Minimal Inductive Clause).
    ///
    /// Returns a (possibly smaller) sub-cube that is still inductive relative
    /// to frame `level - 1` and does not intersect the initial states.
    pub(super) fn generalize_cube(&mut self, cube: &Cube, level: usize) -> Cube {
        self.stats.generalizations += 1;

        // Phase 1: UNSAT core-based shrinking.
        let shrunk = self.down(cube, level);

        // Phase 2: Literal dropping (MIC).
        let original_len = shrunk.len();
        let minimized = self.mic(&shrunk, level);

        // MANDATORY soundness backstop (port of the reference IC3 implementation
        // mic.rs:773-783 `verify_consecution_independent`).
        //
        // ay_sat false-UNSAT in the IC3-tuned incremental solver is the #1
        // soundness risk: a spurious UNSAT lets MIC drop an essential literal,
        // producing a non-inductive lemma that poisons the frames and yields a
        // false Safe. Re-verify EVERY reduced cube on a FRESH, independent
        // ay_sat::Solver (default mode). If the independent check does not
        // confirm consecution, fall back to the un-generalized input cube
        // (which `try_block_cube`/`trivial_block` already proved inductive).
        if minimized.len() < cube.len()
            && self.ts.num_state_vars <= VERIFY_CONSECUTION_INDEPENDENT_MAX_STATE_VARS
        {
            self.stats.cross_check_calls += 1;
            if !self.verify_consecution_independent(&minimized, level) {
                self.stats.cross_check_rejections += 1;
                return cube.clone();
            }
        }

        let dropped = original_len.saturating_sub(minimized.len());
        self.stats.literals_dropped += dropped as u64;

        minimized
    }

    /// UNSAT core-based initial shrinking ("down" in Bradley 2011).
    ///
    /// Maps the UNSAT core from the last relative-inductiveness check
    /// back to current-state variables, producing a smaller sub-cube.
    ///
    /// Domain-restricted (#8443): sets SAT domain before the consecution query.
    fn down(&mut self, cube: &Cube, level: usize) -> Cube {
        // Re-check relative inductiveness to get a fresh UNSAT core.
        let next_cube = self.ts.cube_to_next_state(&cube.literals);
        let mut assumptions = Vec::new();

        // Frame activations for level - 1 AND all higher levels (#8672
        // delta encoding — see solver::collect_frame_activations).
        let frame_act = if level > 0 {
            let acts = self.collect_frame_activations(level - 1);
            let first = acts.first().copied();
            assumptions.extend_from_slice(&acts);
            first
        } else {
            None
        };

        // c' (next-state cube) as assumptions.
        for &lit in &next_cube {
            assumptions.push(lit);
        }

        // Domain restriction (#8443).
        let domain = self
            .ts
            .compute_query_domain(frame_act, &cube.literals, &next_cube);
        self.solver.set_domain(&domain);

        self.stats.sat_calls += 1;
        let result = self.solver.solve_incremental_ic3(&assumptions);
        self.solver.clear_domain();

        match result.into_inner() {
            AssumeResult::Unsat(core, _) => {
                self.stats.core_shrinks += 1;
                // Map core literals back: keep only cube literals whose
                // next-state counterpart appears in the core.
                let core_set: ay_core::kani_compat::DetHashSet<Literal> =
                    core.iter().copied().collect();

                let mut shrunk_lits: Vec<Literal> = Vec::new();
                for (i, &lit) in cube.literals.iter().enumerate() {
                    // Check if the next-state version of this literal is in the core.
                    if i < next_cube.len() && core_set.contains(&next_cube[i]) {
                        shrunk_lits.push(lit);
                    }
                }

                // Also keep any literal from the cube whose negation is in the core
                // (from the negated-cube part of the assumption).
                for &lit in &cube.literals {
                    if core_set.contains(&lit.negated()) && !shrunk_lits.contains(&lit) {
                        shrunk_lits.push(lit);
                    }
                }

                // Safety: the shrunk cube must not be empty and must not
                // intersect init. If shrinking reduced too aggressively,
                // fall back to the original cube.
                if shrunk_lits.is_empty()
                    || self.cube_intersects_init(&Cube::new(shrunk_lits.clone()))
                {
                    return cube.clone();
                }

                Cube::new(shrunk_lits)
            }
            _ => {
                // If the check was SAT or Unknown, no shrinking is possible.
                cube.clone()
            }
        }
    }

    /// MIC: try dropping each literal one at a time.
    ///
    /// For each literal l in the cube, check if the cube without l is still:
    /// 1. Inductive relative to F_{level-1} (no predecessor can reach it)
    /// 2. Does not intersect the initial states
    ///
    /// If both hold, drop l permanently. Process in reverse order so that
    /// dropping one literal doesn't shift indices of earlier elements.
    fn mic(&mut self, cube: &Cube, level: usize) -> Cube {
        let mut current = cube.literals.clone();

        let mut i = current.len();
        while i > 0 {
            i -= 1;
            if current.len() <= 1 {
                break; // Must keep at least one literal.
            }

            // Try removing literal at position i.
            let removed = current.remove(i);
            let candidate = Cube::new(current.clone());

            // Check: does candidate intersect init?
            if self.cube_intersects_init(&candidate) {
                // Must keep this literal to avoid blocking initial states.
                current.insert(i, removed);
                continue;
            }

            // Check: is candidate still inductive relative to F_{level-1}?
            if self.is_inductive_relative(&candidate, level) {
                // Successfully dropped literal — keep the removal.
                continue;
            }

            // CTG (Counterexample-To-Generalization): the plain drop failed
            // because some predecessor in F_{level-1} can reach `candidate`.
            // If that predecessor is itself (recursively) blockable, block it
            // and retry the drop. This is what breaks the SYMMETRY of the
            // parity pair (acc, c0): dropping either alone is non-inductive
            // because the *other* bad equivalence-class is reachable, but once
            // CTG blocks that predecessor class the drop succeeds and MIC
            // converges to the 2-literal parity cube.
            //
            // Gated on `ctg_depth < MAX_CTG_RECURSION` so a `trivial_block`
            // recursion (which raises ctg_depth) does not re-enter CTG here,
            // bounding the recursion. `level > 1` is required because
            // `trivial_block(.., level - 1, ..)` needs a non-zero frame.
            if level > 1 && self.ctg_depth < MAX_CTG_RECURSION {
                let mut ctg_count = 0;
                let mut dropped = false;
                while ctg_count < CTG_MAX {
                    // Extract the predecessor that defeats the drop.
                    let (_inductive, pred) = self.is_inductive_relative_capture(&candidate, level);
                    let pred = match pred {
                        Some(p) => p,
                        None => break,
                    };
                    // Never block an initial state (would be unsound).
                    if self.cube_intersects_init(&pred) {
                        break;
                    }
                    // Recursively block the predecessor at level - 1.
                    let mut tb_limit = CTG_LIMIT;
                    if !self.trivial_block(&pred, level - 1, &mut tb_limit) {
                        break;
                    }
                    ctg_count += 1;
                    // Retry the drop now that the predecessor is blocked.
                    if self.is_inductive_relative(&candidate, level) {
                        dropped = true;
                        self.stats.ctg_successes += 1;
                        break;
                    }
                }
                if dropped {
                    // Keep the removal and move on to the next literal.
                    continue;
                }
            }

            // Cannot drop this literal — restore it.
            current.insert(i, removed);
        }

        Cube::new(current)
    }

    /// Check if a cube is inductive relative to frame `level - 1`.
    ///
    /// A cube c is blocked relative to F if: F /\ T |= not-c'
    /// Equivalently: F /\ T /\ c' is UNSAT.
    ///
    /// Domain-restricted (#8443): sets SAT domain before each MIC literal-drop query.
    /// After each successful drop, the domain is recomputed with the reduced cube,
    /// which may further shrink the variable set (GipSAT Section 3.1, COI recalculation).
    pub(super) fn is_inductive_relative(&mut self, cube: &Cube, level: usize) -> bool {
        let next_cube = self.ts.cube_to_next_state(&cube.literals);
        let mut assumptions = Vec::new();

        // Frame activations for level - 1 AND all higher levels (#8672
        // delta encoding — see solver::collect_frame_activations).
        let frame_act = if level > 0 {
            let acts = self.collect_frame_activations(level - 1);
            let first = acts.first().copied();
            assumptions.extend_from_slice(&acts);
            first
        } else {
            None
        };

        // c' (next state IS in cube).
        for &lit in &next_cube {
            assumptions.push(lit);
        }

        // Domain restriction (#8443): recomputed per MIC query since the cube shrinks.
        let domain = self
            .ts
            .compute_query_domain(frame_act, &cube.literals, &next_cube);
        self.solver.set_domain(&domain);

        self.stats.sat_calls += 1;
        let result = self.solver.solve_incremental_ic3(&assumptions);
        self.solver.clear_domain();
        result.is_unsat()
    }

    /// Like [`is_inductive_relative`], but on a SAT result also returns the
    /// predecessor state cube extracted from the model (CTG support, design
    /// minimal_port (a)).
    ///
    /// Returns `(true, None)` when the cube is inductive relative to
    /// F_{level-1} (the consecution query is UNSAT), `(false, Some(pred))`
    /// when a predecessor in F_{level-1} can reach the cube, and
    /// `(false, None)` on an Unknown SAT result.
    pub(super) fn is_inductive_relative_capture(
        &mut self,
        cube: &Cube,
        level: usize,
    ) -> (bool, Option<Cube>) {
        let next_cube = self.ts.cube_to_next_state(&cube.literals);
        let mut assumptions = Vec::new();

        let frame_act = if level > 0 {
            let acts = self.collect_frame_activations(level - 1);
            let first = acts.first().copied();
            assumptions.extend_from_slice(&acts);
            first
        } else {
            None
        };

        for &lit in &next_cube {
            assumptions.push(lit);
        }

        let domain = self
            .ts
            .compute_query_domain(frame_act, &cube.literals, &next_cube);
        self.solver.set_domain(&domain);

        self.stats.sat_calls += 1;
        let result = self.solver.solve_incremental_ic3(&assumptions);
        self.solver.clear_domain();

        match result.into_inner() {
            AssumeResult::Unsat(..) => (true, None),
            AssumeResult::Sat(model) => {
                let pred = self.ts.extract_state_cube(&model);
                (false, Some(Cube::new(pred)))
            }
            _ => (false, None),
        }
    }

    /// Recursively block a counterexample-to-generalization (CTG) predecessor
    /// (design minimal_port (b); port of the reference IC3 implementation `trivial_block`).
    ///
    /// Attempts to block `cube` at `level`. If `cube` is inductive relative to
    /// F_{level-1}, it is generalized (depth-gated so the inner CTG loop is
    /// disabled during recursion) and the resulting lemma is added to the
    /// frames; returns `true`. Otherwise the offending predecessor is extracted
    /// and we recurse one frame lower, until either the cube is blocked or the
    /// `limit` budget is exhausted.
    ///
    /// SOUNDNESS: a lemma is added only after `is_inductive_relative` passes AND
    /// the generalized cube does not intersect Init. The generalization itself
    /// runs the independent-consecution cross-check via `generalize_cube`.
    pub(super) fn trivial_block(&mut self, cube: &Cube, level: usize, limit: &mut usize) -> bool {
        if level == 0 || *limit == 0 {
            return false;
        }
        // Never block an initial state.
        if self.cube_intersects_init(cube) {
            return false;
        }
        *limit -= 1;
        loop {
            if self.is_inductive_relative(cube, level) {
                // Generalize, raising ctg_depth so the inner CTG loop in mic()
                // is disabled (mirrors the reference implementation's recursive `mic` at raised depth).
                self.ctg_depth += 1;
                let generalized = self.generalize_cube(cube, level);
                self.ctg_depth -= 1;

                // Reject init-intersecting generalizations (unsound).
                if self.cube_intersects_init(&generalized) {
                    return false;
                }
                self.add_blocked_clause_to_frames(&generalized.to_clause(), level);
                self.stats.cubes_blocked += 1;
                return true;
            }
            if *limit == 0 {
                return false;
            }
            // Extract the predecessor and recurse one frame lower.
            let (_inductive, pred) = self.is_inductive_relative_capture(cube, level);
            match pred {
                Some(p) => {
                    if !self.trivial_block(&p, level - 1, limit) {
                        return false;
                    }
                }
                None => return false,
            }
        }
    }

    /// Independent-consecution cross-check (design Step 1 soundness gate; port
    /// of the reference IC3 implementation `verify_consecution_independent`, mic.rs:773-783).
    ///
    /// Re-verifies that `cube` is inductive relative to F_{level-1} on a FRESH
    /// `ay_sat::Solver` constructed from scratch in DEFAULT mode (full BCP, no
    /// IC3-specific tuning, no shared incremental state). This is independent of
    /// the IC3-tuned `self.solver`, so a false-UNSAT bug there cannot also
    /// corrupt this check. Mirrors the engine's own (absolute) consecution
    /// query: F_{level-1} /\ T /\ cube' must be UNSAT.
    ///
    /// Returns `true` if consecution is confirmed (UNSAT), `false` otherwise.
    fn verify_consecution_independent(&self, cube: &Cube, level: usize) -> bool {
        let mut solver = ay_sat::Solver::new(self.ts.total_vars);

        // Transition relation T.
        for clause in &self.ts.trans_clauses {
            solver.add_clause(clause.clone());
        }

        // F_{level-1} blocking clauses: under delta encoding these live in
        // frames[level-1..] (collect_frame_activations(level-1)). The
        // current-state Init formula is intentionally NOT added here: the
        // engine's own consecution query (is_inductive_relative) likewise
        // activates only the frame blocking clauses, so this matches the exact
        // property the engine relied on when it accepted the drop.
        if level >= 1 {
            for frame in self.frames.iter().skip(level - 1) {
                for clause in &frame.blocked_clauses {
                    solver.add_clause(clause.clone());
                }
            }
        }

        // cube' (next-state literals) as assumptions.
        let next_cube = self.ts.cube_to_next_state(&cube.literals);
        let result = solver.solve_with_assumptions(&next_cube);
        result.is_unsat()
    }

    /// Check if a cube intersects the initial states.
    /// Returns true if Init /\ cube is SAT.
    pub(super) fn cube_intersects_init(&mut self, cube: &Cube) -> bool {
        let assumptions: Vec<Literal> = cube.literals.clone();
        self.stats.sat_calls += 1;
        let result = self.init_solver.solve_incremental_ic3(&assumptions);
        result.is_sat()
    }
}
