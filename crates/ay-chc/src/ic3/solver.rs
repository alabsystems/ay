// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Main IC3 solver for clause-level hardware model checking (#8211).
//!
//! Implements the core IC3/PDR algorithm (Bradley VMCAI 2011) using ay-sat
//! for all SAT queries. The solver maintains a sequence of frames, each
//! over-approximating the reachable states at depth i, and iteratively
//! strengthens them by blocking cubes (bad states + predecessors).
//!
//! # Algorithm overview
//!
//! 1. Check if Init ∧ Bad is SAT (immediate counterexample at depth 0)
//! 2. Loop:
//!    a. Find a bad cube in the current frontier frame
//!    b. Block it by finding inductive generalizations
//!    c. If blocking fails at level 0, return counterexample
//!    d. If no more bad cubes, push to next frame
//! 3. Propagate blocked clauses forward
//! 4. Check for fixpoint (F_i = F_{i+1} → invariant found)

use std::collections::BinaryHeap;
use std::rc::Rc;

use super::cube::{Cube, Ic3Frame, Ic3Obligation, PriorityObligation};
use super::stats::Ic3Stats;
use super::transition_system::BitLevelTransitionSystem;
use ay_sat::{AssumeResult, Literal, Variable};

/// Result of IC3 model checking.
#[derive(Debug)]
pub(crate) enum Ic3Result {
    /// The property is safe: no bad state is reachable.
    /// Contains the invariant frame level (all frames up to this level
    /// together form an inductive invariant).
    Safe {
        /// Frame level at which the fixpoint was detected.
        invariant_level: usize,
    },
    /// The property is unsafe: a bad state is reachable.
    /// Contains a counterexample trace of state cubes from init to bad.
    Unsafe {
        /// Sequence of state cubes forming the counterexample trace.
        /// trace[0] is an initial state, trace[last] satisfies bad.
        trace: Vec<Cube>,
    },
    /// The solver could not determine the result (e.g., resource limit).
    Unknown,
}

/// Clause-level IC3 solver using ay-sat as the SAT backend.
pub(crate) struct Ic3Solver {
    /// The bit-level transition system being checked.
    pub(super) ts: BitLevelTransitionSystem,
    /// Frame sequence: frames[i] over-approximates states reachable in ≤i steps.
    /// frames[0] contains Init constraints.
    pub(super) frames: Vec<Ic3Frame>,
    /// SAT solver for init-state queries (Init ∧ cube).
    pub(super) init_solver: ay_sat::Solver,
    /// Main SAT solver for transition queries (F_k ∧ T ∧ assumptions).
    /// Frame clauses are asserted with activation literals.
    pub(super) solver: ay_sat::Solver,
    /// Reusable activation variable for temporary clause management (#8443).
    ///
    /// GipSAT pattern (Theorem 4.1): a single activation variable is allocated
    /// once and reused across all IC3 queries. Temporary clauses (constraint
    /// clauses for consecution checks) are guarded by this variable. Between
    /// queries, `clean_temporary_clauses()` uses push/pop scopes to remove
    /// temporary clauses without solver reset.
    ///
    /// This avoids allocating a new activation variable per query (the pre-#8443
    /// pattern), reducing memory growth and improving cache locality in
    /// long-running IC3 instances.
    constrain_activation: Variable,
    /// Statistics counters.
    pub(super) stats: Ic3Stats,
    /// Monotonic counter for deterministic obligation ordering.
    next_seq_id: u64,
    /// CTG (Counterexample-To-Generalization) recursion depth guard.
    ///
    /// The outermost MIC call runs at depth 0 (full CTG enabled). When
    /// `trivial_block` recurses into `generalize_cube` it bumps this to 1,
    /// which disables the inner CTG loop in `mic()` (gated on
    /// `ctg_depth < MAX_CTG_RECURSION`), bounding recursion and preventing
    /// exponential blowup. Mirrors the reference IC3 implementation's `ctg_recursion_depth`.
    pub(super) ctg_depth: usize,
    /// Verbose tracing output.
    verbose: bool,
    /// Optional hard wall-clock deadline. Checked only at solve/block loop
    /// heads; on expiry `solve()` returns [`Ic3Result::Unknown`] -- never a
    /// truncated `Safe`/`Unsafe`. `None` = no time bound (previous behavior).
    deadline: Option<ay_core::time::Instant>,
}

impl Ic3Solver {
    /// Create a new IC3 solver for the given transition system.
    pub(crate) fn new(ts: BitLevelTransitionSystem, verbose: bool) -> Self {
        let total_vars = ts.total_vars;

        // Init solver: contains only initial state constraints.
        // IC3 init queries are Init ∧ cube checks, using solve_with_assumptions.
        // Enable IC3 mode for conservative learned clause GC and VSIDS
        // persistence across the many incremental queries (#8643).
        let mut init_solver = ay_sat::Solver::new(total_vars);
        init_solver.set_ic3_mode();
        for clause in &ts.init_clauses {
            init_solver.add_clause(clause.clone());
        }

        // Main solver: contains the transition relation.
        // Frame clauses are added incrementally with activation literals.
        let mut solver = ay_sat::Solver::new(total_vars);

        // Configure for IC3 incremental workload (#8643, #8430, #8569):
        //
        // set_ic3_mode() is the single entry point that configures the solver
        // for IC3/PDR workloads. It disables all features unnecessary for IC3
        // queries (inprocessing, preprocessing, LRAT proofs, chrono-BT, cold
        // restarts, walk/rephase/flip search, DIP-ERCL) and enables IC3-
        // specific optimizations (conservative learned clause GC, VSIDS
        // activity persistence across calls, stable mode lock for EVSIDS).
        //
        // Previously only set_incremental_mode() was called, which only
        // disabled destructive inprocessing. This left the aggressive
        // between_solve_reduce() path active (deleting 50% of learned clauses
        // when count > 3x irredundant), CHB state being reset between calls,
        // and the full reset path being used instead of the lightweight
        // incremental reset. The result was that learned clauses, VSIDS
        // activity, and phase saving did not persist between IC3 calls (#8643).
        solver.set_ic3_mode();

        for clause in &ts.trans_clauses {
            solver.add_clause(clause.clone());
        }

        // Allocate a reusable activation variable for temporary clauses (#8443).
        // GipSAT (mod.rs:77): constrain_act = Var::CONST, then new_var() returns
        // the previous constrain_act. AY adaptation: allocate one variable that
        // will be used as a guard for constraint clauses across all queries.
        let constrain_activation = solver.new_var();

        // Register the activation variable with the SAT solver so that
        // solve_incremental_ic3() automatically includes it in assumptions
        // and constrained clauses are properly managed (#8662).
        solver.set_constrain_activation(constrain_activation);

        Self {
            ts,
            frames: Vec::new(),
            init_solver,
            solver,
            constrain_activation,
            stats: Ic3Stats::default(),
            next_seq_id: 0,
            ctg_depth: 0,
            verbose,
            deadline: None,
        }
    }

    /// Attach an optional hard wall-clock deadline (builder style, so existing
    /// `Ic3Solver::new(..)` call sites are unaffected). On expiry the solver
    /// returns [`Ic3Result::Unknown`]; it never truncates the search into a
    /// `Safe`/`Unsafe` verdict.
    #[must_use]
    pub(crate) fn with_deadline(mut self, deadline: Option<ay_core::time::Instant>) -> Self {
        self.deadline = deadline;
        self
    }

    /// True once the configured deadline has passed. Checked only at loop heads
    /// (see [`Ic3Solver::solve`] and `block_all_bad`), where returning `Unknown`
    /// cannot corrupt a verdict: `Safe` is only produced after a completed
    /// `propagate()` fixpoint and `Unsafe` only from a verified Init-reaching cube.
    #[inline]
    fn resource_exhausted(&self) -> bool {
        self.deadline
            .is_some_and(|d| ay_core::time::Instant::now() >= d)
    }

    /// Run the IC3 algorithm to check if any bad state is reachable.
    pub(crate) fn solve(&mut self) -> Ic3Result {
        // Step 1: Check Init ∧ Bad — immediate counterexample?
        if self.init_intersects_bad() {
            let bad_cube = Cube::new(self.ts.bad_literals.clone());
            self.stats.cex_traces += 1;
            self.collect_domain_bcp_stats();
            return Ic3Result::Unsafe {
                trace: vec![bad_cube],
            };
        }

        // Create frame F_0 (initial states) and F_1 (first frontier).
        self.new_frame(); // F_0
        self.new_frame(); // F_1

        // Block Bad in F_0: initial states must not satisfy Bad.
        // (Already guaranteed by init_intersects_bad check above.)

        // Main loop: strengthen frames and push frontier.
        loop {
            // Honor the optional deadline at the loop head -- a safe point where
            // returning Unknown cannot be mistaken for a Safe/Unsafe verdict.
            if self.resource_exhausted() {
                self.collect_domain_bcp_stats();
                return Ic3Result::Unknown;
            }
            let k = self.frontier_level();

            // Try to find and block all bad cubes at the frontier.
            match self.block_all_bad(k) {
                BlockResult::Blocked => {
                    // All bad cubes blocked at level k.
                    // Propagate clauses forward and check for fixpoint.
                    if self.propagate() {
                        let level = self.fixpoint_level();
                        self.collect_domain_bcp_stats();
                        if self.verbose {
                            tracing::info!("IC3: fixpoint at level {level}, {}", self.stats);
                        }
                        return Ic3Result::Safe {
                            invariant_level: level,
                        };
                    }
                    // No fixpoint yet; add a new frame and continue.
                    self.new_frame();
                    if self.verbose {
                        tracing::info!("IC3: new frame {}, {}", self.frontier_level(), self.stats);
                    }
                }
                BlockResult::Counterexample(trace) => {
                    self.stats.cex_traces += 1;
                    self.collect_domain_bcp_stats();
                    if self.verbose {
                        tracing::info!(
                            "IC3: counterexample of length {}, {}",
                            trace.len(),
                            self.stats
                        );
                    }
                    return Ic3Result::Unsafe { trace };
                }
                BlockResult::Unknown => {
                    self.collect_domain_bcp_stats();
                    if self.verbose {
                        tracing::info!("IC3: unknown (SAT timeout), {}", self.stats);
                    }
                    return Ic3Result::Unknown;
                }
            }
        }
    }

    /// Collect domain BCP statistics from the SAT solver (#8430).
    ///
    /// Transfers the SAT-level domain_bcp_skips/calls counters into
    /// the IC3 stats for unified reporting.
    fn collect_domain_bcp_stats(&mut self) {
        let (skips, calls) = self.solver.domain_bcp_stats();
        self.stats.domain_bcp_skips = skips;
        self.stats.domain_bcp_calls = calls;
    }

    /// The current frontier frame level (highest non-infinity frame).
    fn frontier_level(&self) -> usize {
        self.frames.len() - 1
    }

    /// Create a new frame with a fresh activation literal.
    fn new_frame(&mut self) {
        let act_var = self.solver.new_var();
        let activation = Literal::positive(act_var);
        self.frames.push(Ic3Frame::new(activation));
        self.stats.frames_created += 1;
    }

    /// Check if Init ∧ Bad is satisfiable.
    fn init_intersects_bad(&mut self) -> bool {
        let assumptions: Vec<Literal> = self.ts.bad_literals.clone();
        self.stats.sat_calls += 1;
        let result = self.init_solver.solve_incremental_ic3(&assumptions);
        result.is_sat()
    }

    /// Try to block all bad cubes reachable at the frontier frame.
    ///
    /// Uses a priority queue of proof obligations, processing lower levels first.
    /// Returns `Blocked` if all obligations are resolved, or `Counterexample`
    /// if a trace to a bad state from Init is found.
    fn block_all_bad(&mut self, k: usize) -> BlockResult {
        let mut obligations: BinaryHeap<PriorityObligation> = BinaryHeap::new();

        // Find bad cubes in the frontier frame.
        while let Some(bad_cube) = self.get_bad_cube(k) {
            if self.resource_exhausted() {
                return BlockResult::Unknown;
            }
            let seq_id = self.next_seq_id();
            obligations.push(PriorityObligation(Ic3Obligation::new(
                bad_cube, k, 0, seq_id, None,
            )));

            // Process obligations in priority order (lowest level first).
            while let Some(PriorityObligation(ob)) = obligations.pop() {
                if self.resource_exhausted() {
                    return BlockResult::Unknown;
                }
                self.stats.obligations_processed += 1;

                if ob.level == 0 {
                    // At level 0 we must verify the cube actually satisfies
                    // Init before declaring a counterexample. The predecessor
                    // SAT extraction at higher levels does not guarantee
                    // Init-membership of the extracted state -- only that it
                    // satisfies F_{level-1}. If the cube is NOT initial we
                    // block it at frame 0 and continue the obligation loop;
                    // this strengthens F_0 with `¬cube` so we will not waste
                    // work re-deriving the same non-initial cube.
                    self.stats.sat_calls += 1;
                    let init_result = self.init_solver.solve_incremental_ic3(&ob.cube.literals);
                    match init_result.into_inner() {
                        AssumeResult::Sat(_) => {
                            // Real counterexample: cube is in Init.
                            let trace = self.reconstruct_trace(&ob);
                            return BlockResult::Counterexample(trace);
                        }
                        AssumeResult::Unsat(..) => {
                            // Cube does not satisfy Init. Block at level 0.
                            let clause = ob.cube.to_clause();
                            self.add_blocked_clause_to_frames(&clause, 0);
                            self.stats.cubes_blocked += 1;
                            // Fall through to process the next obligation
                            // from the heap (do NOT re-enqueue this one).
                            continue;
                        }
                        AssumeResult::Unknown | _ => {
                            // Cannot determine -- propagate Unknown.
                            return BlockResult::Unknown;
                        }
                    }
                }

                // Try to block this cube at its level.
                match self.try_block_cube(&ob.cube, ob.level) {
                    TryBlockResult::Blocked(generalized) => {
                        // Cube (generalized) is blocked at ob.level.
                        // Add the blocking clause to frames 1..=ob.level.
                        let clause = generalized.to_clause();
                        self.add_blocked_clause_to_frames(&clause, ob.level);
                        self.stats.cubes_blocked += 1;
                    }
                    TryBlockResult::Predecessor(pred_cube) => {
                        // Found a predecessor: push obligations for the predecessor
                        // at level-1, and re-enqueue the current obligation.
                        //
                        // The predecessor's parent is the current obligation `ob`
                        // (wrapped in Rc so the chain can be walked at trace
                        // reconstruction time). The retry obligation preserves
                        // `ob`'s own parent link so the chain is not broken.
                        let parent_rc = Rc::new(ob.clone());
                        let seq_id_pred = self.next_seq_id();
                        obligations.push(PriorityObligation(Ic3Obligation::new(
                            pred_cube,
                            ob.level - 1,
                            ob.depth + 1,
                            seq_id_pred,
                            Some(parent_rc),
                        )));
                        let seq_id_retry = self.next_seq_id();
                        let retry_parent = ob.parent.clone();
                        obligations.push(PriorityObligation(Ic3Obligation::new(
                            ob.cube,
                            ob.level,
                            ob.depth,
                            seq_id_retry,
                            retry_parent,
                        )));
                    }
                    TryBlockResult::Unknown => {
                        // SAT solver gave Unknown -- propagate upward so
                        // `solve()` returns `Ic3Result::Unknown` instead of
                        // fabricating a counterexample.
                        return BlockResult::Unknown;
                    }
                }
            }
        }

        BlockResult::Blocked
    }

    /// Find a bad cube in frame `level`: check if F_level ∧ Bad is SAT.
    ///
    /// Returns a cube over state variables that satisfies both the frame
    /// constraints and the bad-state property, or None if no such state exists.
    ///
    /// Domain-restricted (#8443): sets SAT domain to frame activation + bad
    /// literals + COI before the query, then clears it after.
    fn get_bad_cube(&mut self, level: usize) -> Option<Cube> {
        let mut assumptions = Vec::new();

        // Activate frame constraints for this level AND all higher levels
        // (#8672 delta encoding: clauses at level j are stored only in
        // frames[j], so F_level = ⋃_{j >= level} frames[j]).
        let frame_acts = self.collect_frame_activations(level);
        let frame_act = frame_acts.first().copied();
        assumptions.extend_from_slice(&frame_acts);

        // Assert bad-state literals.
        for &lit in &self.ts.bad_literals {
            assumptions.push(lit);
        }

        // Domain restriction: bad-state check domain = V(frame_act) ∪ V(bad) ∪ COI(bad).
        //
        // CORRECTNESS FIX (#ctg-bad-domain): the bad property may be a Tseitin
        // auxiliary variable whose support (the state vars it is DEFINED over)
        // is reached only through the cone-of-influence. Previously this passed
        // `&[]` as the next-cube, so `compute_query_domain` computed `COI(∅)=∅`
        // and the domain excluded the property's support. For an aux-var bad
        // like `bad <=> acc ⊕ c0`, that left `acc`/`c0` outside the domain, so
        // the defining clauses were not enforced and the solver could report
        // `bad=true` with `acc=c0=0` — fabricating the initial state as a bad
        // state (then "blocking" init, corrupting the frames). Passing
        // `bad_literals` as the COI seed pulls the property's support
        // (`COI(bad) ⊇ {acc, c0}`) into the domain so the definition is honored.
        let bad_lits = self.ts.bad_literals.clone();
        let domain = self
            .ts
            .compute_query_domain(frame_act, &bad_lits, &bad_lits);
        self.solver.set_domain(&domain);

        self.stats.sat_calls += 1;
        let result = self.solver.solve_incremental_ic3(&assumptions);
        self.solver.clear_domain();

        match result.into_inner() {
            AssumeResult::Sat(model) => {
                let state_cube = self.ts.extract_state_cube(&model);
                Some(Cube::new(state_cube))
            }
            _ => None,
        }
    }

    /// Try to block a cube at the given level.
    ///
    /// Checks relative inductiveness: F_{level-1} ∧ T ∧ cube' is UNSAT?
    /// - If UNSAT: the cube is inductive relative to F_{level-1}. Generalize and block.
    /// - If SAT: extract the predecessor state (a cube in F_{level-1} that can reach cube).
    ///
    /// Domain-restricted (#8443): sets SAT domain before each consecution query.
    fn try_block_cube(&mut self, cube: &Cube, level: usize) -> TryBlockResult {
        let next_cube = self.ts.cube_to_next_state(&cube.literals);
        let mut assumptions = Vec::new();

        // Frame activations for level - 1 AND all higher levels (#8672
        // delta encoding). F_{level-1} is activated by assuming the
        // activation literal of every frame j with j >= level - 1.
        let frame_act = if level > 0 {
            let acts = self.collect_frame_activations(level - 1);
            let first = acts.first().copied();
            assumptions.extend_from_slice(&acts);
            first
        } else {
            None
        };

        // cube' (next state IS in cube).
        for &lit in &next_cube {
            assumptions.push(lit);
        }

        // Domain restriction (#8443): domain = V(frame_act) ∪ V(cube) ∪ V(next_cube) ∪ COI(next_cube).
        let domain = self
            .ts
            .compute_query_domain(frame_act, &cube.literals, &next_cube);
        self.solver.set_domain(&domain);

        self.stats.sat_calls += 1;
        let result = self.solver.solve_incremental_ic3(&assumptions);
        self.solver.clear_domain();

        match result.into_inner() {
            AssumeResult::Unsat(..) => {
                // Cube is inductive relative to F_{level-1}. Generalize it.
                let generalized = self.generalize_cube(cube, level);
                TryBlockResult::Blocked(generalized)
            }
            AssumeResult::Sat(model) => {
                // Found a predecessor: extract state from the model.
                let pred_lits = self.ts.extract_state_cube(&model);
                TryBlockResult::Predecessor(Cube::new(pred_lits))
            }
            AssumeResult::Unknown | _ => {
                // Soundness: we cannot conclude the cube is blocked, nor do
                // we have a model from which to extract a predecessor.
                // Propagate Unknown upward — fabricating the cube as its own
                // predecessor (the pre-fix behavior) would walk it down to
                // level 0 and yield a spurious `Ic3Result::Unsafe`.
                TryBlockResult::Unknown
            }
        }
    }

    /// Add a blocking clause at level `level` under delta encoding (#8672).
    ///
    /// The clause is stored in `frames[level].blocked_clauses` only (NOT in
    /// every frame 1..=level as it was pre-#8672). The logical contents of
    /// F_i at any level i <= level still include this clause — see
    /// [`Ic3Frame`] docs and `collect_frame_activations`.
    ///
    /// The clause is asserted in the SAT solver guarded by this frame's
    /// activation literal: `(¬frames[level].activation ∨ clause)`. Queries
    /// at level i <= level assume the activation literals of frames i..last,
    /// which transitively activates this clause.
    ///
    /// This matches Z3 Spacer's single-storage convention from
    /// `reference/z3/src/muz/spacer/spacer_legacy_frames.cpp` (`add_lemma` +
    /// `propagate_to_next_level`) and prevents the O(lemmas * depth) memory
    /// growth that the pre-#8672 duplicated-storage implementation caused.
    pub(super) fn add_blocked_clause_to_frames(&mut self, clause: &[Literal], level: usize) {
        // NOTE: level == 0 is permitted (#fix-init-check). A cube reaching
        // level 0 in `block_all_bad` that does NOT satisfy Init must still be
        // blocked at frame 0 so the obligation loop does not re-derive it.
        // Only out-of-range levels are rejected here.
        if level >= self.frames.len() {
            return;
        }

        // Deduplicate against existing storage at level j >= `level`. Under
        // delta encoding, a clause at level j is active at all levels
        // 1..=j, so if this lemma is already stored at level `level` or
        // above, we do not add it again (prevents unbounded duplication
        // from the priority queue re-dispatching the same obligation or
        // from generalization producing the same blocking clause twice —
        // see Spacer's `add_lemma` guard `!m_invariants.contains(lemma)` in
        // reference/z3/src/muz/spacer/spacer_legacy_frames.cpp:126).
        if self
            .frames
            .iter()
            .skip(level)
            .any(|frame| frame.blocked_clauses.iter().any(|c| c.as_slice() == clause))
        {
            return;
        }
        for frame in self.frames.iter_mut().take(level) {
            frame
                .blocked_clauses
                .retain(|existing| existing.as_slice() != clause);
        }

        let activation = self.frames[level].activation;
        // Assert: activation => clause, i.e. (¬activation ∨ l1 ∨ l2 ∨ ... ∨ ln)
        let mut activated_clause = Vec::with_capacity(clause.len() + 1);
        activated_clause.push(activation.negated());
        activated_clause.extend_from_slice(clause);
        self.solver.add_clause(activated_clause);

        self.frames[level].add_blocked_clause(clause.to_vec());
    }

    /// Collect activation literals for a query at level `level` (#8672).
    ///
    /// Under delta encoding, F_level = Init ∪ {clauses at levels >= level}.
    /// To activate all clauses at levels j >= level in a SAT query, we assume
    /// the activation literals of frames[level..]. This replaces the pre-#8672
    /// pattern of asserting only `frames[level].activation`, which relied on
    /// every clause being duplicated into every lower frame.
    pub(super) fn collect_frame_activations(&self, level: usize) -> Vec<Literal> {
        if level >= self.frames.len() {
            return Vec::new();
        }
        self.frames[level..]
            .iter()
            .map(|frame| frame.activation)
            .collect()
    }

    /// Reconstruct a counterexample trace from a failed obligation.
    ///
    /// `obligation` is the level-0 obligation whose cube has been shown to
    /// satisfy Init. Walking its parent chain produces the predecessor →
    /// successor sequence; reversing it gives the documented contract
    /// `trace[0] ∈ Init` ... `trace[last] ∈ Bad` (see [`Ic3Result::Unsafe`]
    /// docs at solver.rs:42-46).
    fn reconstruct_trace(&self, obligation: &Ic3Obligation) -> Vec<Cube> {
        // Collect cubes from leaf (level-0) up the parent chain to the
        // original bad obligation (which has parent = None).
        let mut chain = vec![obligation.cube.clone()];
        let mut cur = obligation.parent.clone();
        while let Some(p) = cur {
            chain.push(p.cube.clone());
            cur = p.parent.clone();
        }
        // chain[0] is the level-0 (Init) cube, chain[last] is the bad cube.
        // This already matches the documented contract.
        chain
    }

    /// Get the next monotonic sequence ID.
    fn next_seq_id(&mut self) -> u64 {
        let id = self.next_seq_id;
        self.next_seq_id += 1;
        id
    }

    /// Find the fixpoint level (where propagation detected F_i = F_{i+1}).
    fn fixpoint_level(&self) -> usize {
        // Return the last frame level; propagate() ensures correctness.
        self.frames.len().saturating_sub(1)
    }

    /// Solve with temporary constraint clauses using the reusable activation variable (#8443).
    ///
    /// GipSAT pattern: adds constraint clauses guarded by `constrain_activation`, then
    /// solves with `constrain_activation` as an assumption. After solving, removes the
    /// temporary clauses using push/pop scopes.
    ///
    /// `constraints` is a list of clause-form constraints. Each constraint clause C
    /// is added as `(constrain_activation ∨ ¬l1 ∨ ¬l2 ∨ ...)` — i.e., the
    /// activation literal guards the constraint.
    ///
    /// This avoids allocating a new activation variable per query and reduces
    /// memory growth from temporary learned clauses containing stale activations.
    ///
    /// Returns the SAT result with domain restriction already applied and cleared.
    pub(super) fn solve_with_domain_and_constraints(
        &mut self,
        assumptions: &[Literal],
        constraints: &[Vec<Literal>],
        domain: &[Variable],
    ) -> ay_sat::VerifiedAssumeResult {
        // Push a scope to isolate temporary clauses.
        self.solver.push();

        // Add constraint clauses guarded by the activation variable.
        let act_neg = Literal::negative(self.constrain_activation);
        for constraint in constraints {
            let mut clause = Vec::with_capacity(constraint.len() + 1);
            clause.push(act_neg);
            clause.extend_from_slice(constraint);
            self.solver.add_clause(clause);
        }

        // Build full assumptions: activation literal + caller assumptions.
        let mut full_assumptions = Vec::with_capacity(assumptions.len() + 1);
        if !constraints.is_empty() {
            full_assumptions.push(Literal::positive(self.constrain_activation));
        }
        full_assumptions.extend_from_slice(assumptions);

        // Set domain restriction.
        self.solver.set_domain(domain);

        self.stats.sat_calls += 1;
        let result = self.solver.solve_incremental_ic3(&full_assumptions);

        // Clear domain and pop scope to remove temporary clauses.
        self.solver.clear_domain();
        let _ = self.solver.pop();

        result
    }

    /// Access the stats for reporting.
    pub(crate) fn stats(&self) -> &Ic3Stats {
        &self.stats
    }

    /// Extract the inductive invariant as CNF clauses over current-state
    /// variables (#8211 wiring).
    ///
    /// After [`solve`](Self::solve) returns `Safe { invariant_level }`, the
    /// inductive invariant `I` is `Init /\ (conjunction of all blocked clauses
    /// in frames[j] for j >= invariant_level)` (the delta-encoded frame
    /// representation). Each blocked clause is a disjunction of literals over
    /// the state latches. This returns that clause set so a caller can
    /// back-translate it into a word-level invariant (which is then
    /// independently re-validated — the clauses are NOT trusted here).
    pub(crate) fn invariant_clauses(&self, level: usize) -> Vec<Vec<Literal>> {
        let mut out = Vec::new();
        for frame in self.frames.iter().skip(level) {
            for clause in &frame.blocked_clauses {
                out.push(clause.clone());
            }
        }
        out
    }
}

/// Result of trying to block all bad cubes at a level.
enum BlockResult {
    /// All bad cubes blocked successfully.
    Blocked,
    /// Found a counterexample trace from Init to Bad.
    Counterexample(Vec<Cube>),
    /// SAT solver returned Unknown (e.g., resource limit) -- propagate
    /// to the top-level as `Ic3Result::Unknown` rather than fabricating
    /// a counterexample.
    Unknown,
}

/// Result of trying to block a single cube.
enum TryBlockResult {
    /// Cube was blocked (possibly generalized).
    Blocked(Cube),
    /// Found a predecessor cube that needs to be blocked at a lower level.
    Predecessor(Cube),
    /// SAT solver returned Unknown -- the cube cannot be blocked nor can
    /// a predecessor be extracted. Caller must propagate this upward
    /// instead of fabricating a predecessor.
    Unknown,
}
