// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDR solve initialization: problem validation, init safety check,
//! must-summary initialization, symbolic equality propagation, and
//! startup invariant discovery.

use super::*;

impl PdrSolver {
    /// Initialize the solver state and run pre-loop checks.
    ///
    /// Returns `Some(result)` for early termination (init unsafe, acyclic safety,
    /// invalid problem, startup discovery proved safety). Returns `None` to
    /// proceed to the main PDR loop.
    pub(super) fn solve_init(&mut self) -> Option<PdrResult> {
        // Set the solve deadline. A caller-supplied timeout takes precedence;
        // otherwise a generous DEFAULT SAFETY deadline is ALWAYS installed. This
        // is load-bearing: panic-freedom (and other proof-seeking) obligations
        // run WITHOUT a timeout — they want a proof, not Unknown — so without a
        // default the wall-clock deadline is never set, the propagate-level
        // deadline poll (TheoryExtension::propagate_impl) can never fire, and a
        // divergent conflict-free/decision-free level-0 theory-propagation churn
        // spins at 100% CPU forever, hanging the whole verification gate. With
        // the default, such a solve terminates fail-closed to Unknown (never a
        // fabricated Sat/Unsat) after DEFAULT_SAFETY_DEADLINE, which is set far
        // above any legitimate proof time so it only ever kills a true spin.
        const DEFAULT_SAFETY_DEADLINE: std::time::Duration = std::time::Duration::from_mins(5);
        let config_deadline = ay_core::time::Instant::now()
            + self.config.solve_timeout.unwrap_or(DEFAULT_SAFETY_DEADLINE);
        // Honor any TIGHTER ambient absolute deadline the embedding lane already
        // installed for this obligation, taking the MINIMUM (fail-closed — this
        // only ever SHORTENS the deadline). Two sources are consulted:
        //   * `current_thread_solve_deadline()` — a thread-scoped deadline the
        //     embedder installs ONCE at obligation entry (`ScopedSolveDeadline`).
        //     Because it is ABSOLUTE and thread-wide, every INNER `PdrSolver::solve`
        //     the engine spawns for this obligation (portfolio/validation/probe
        //     sub-solves) inherits the SAME wall-clock ceiling instead of being
        //     re-granted a fresh full budget each time it re-enters `solve_init`
        //     (the per-round fresh-budget regression class, cf. 88c66631).
        //   * `self.smt.current_global_deadline()` — a deadline already pushed
        //     onto THIS `SmtContext` by an enclosing solve; without the min the
        //     line below (`set_global_solve_deadline`) would CLOBBER a tighter
        //     enclosing deadline with our looser (up to 300s default) one.
        // A caller that wants the full default simply installs neither.
        self.solve_deadline = [
            Some(config_deadline),
            crate::smt::current_thread_solve_deadline(),
            self.smt.current_global_deadline(),
        ]
        .into_iter()
        .flatten()
        .min();
        // Plumb the absolute solve deadline down to the SMT context so EVERY
        // check_sat (startup discovery, portfolio engines, proof validation —
        // not just the main blocking loop) honors it, even when invoked without
        // a per-query timeout. Without this a single unbounded query on an
        // integer-modulo CHC could spin for minutes/hours past solve_timeout.
        self.smt.set_global_solve_deadline(self.solve_deadline);

        // Import cross-engine lemma pool hints (#7919).
        // Convert SharedLemma entries to LemmaHint and merge into user_hints
        // so they flow through the standard hint validation pipeline.
        if let Some(pool) = self.config.lemma_hints.take() {
            if !pool.is_empty() {
                let hint_count = pool.len();
                let hints = pool.to_hint_vec();
                self.config.user_hints.extend(hints);
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Imported {} cross-engine lemma hints from LemmaPool (#7919)",
                        hint_count
                    );
                }
            }
        }

        // Validate problem first
        if let Err(e) = self.problem.validate() {
            if self.config.verbose {
                safe_eprintln!("PDR: Invalid CHC problem: {}", e);
            }
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }

        // Reject problems with unsupported predicate sorts. PDR's SMT backend
        // supports Int/Real/Bool/BV/Array/Datatype; other sorts are not yet supported.
        // BV was previously rejected (#5523) but BV evaluation support was
        // added (sign_extend, zero_extend, repeat). Portfolio validation catches
        // unsound results, so PDR can attempt BV problems safely (#5595, #5644).
        // Array sorts are accepted (#6047): the underlying ay-dpll solver handles
        // array theory (select/store axioms, extensionality). Array-sorted state
        // vars are excluded from cubes/lemmas; the scalarization preprocessing
        // pass converts constant-index arrays to scalars before PDR runs.
        // Variable-index arrays pass through as Array-sorted state variables
        // and are handled via model-value substitution in MBP.
        for pred in self.problem.predicates() {
            for sort in &pred.arg_sorts {
                match sort {
                    ChcSort::Int
                    | ChcSort::Real
                    | ChcSort::Bool
                    | ChcSort::BitVec(_)
                    | ChcSort::Array(_, _)
                    | ChcSort::Datatype { .. } => {}
                    unsupported => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Unsupported predicate sort {:?} in {}, returning Unknown",
                                unsupported,
                                pred.name
                            );
                        }
                        return Some(self.finish_with_result_trace(PdrResult::Unknown));
                    }
                }
            }
        }

        // Configuration preconditions — programmer errors, must always fire (#3095).
        assert!(self.config.max_frames > 0, "PDR: max_frames must be >= 1");
        assert!(
            self.config.max_iterations > 0,
            "PDR: max_iterations must be >= 1"
        );
        assert!(
            self.config.max_obligations > 0,
            "PDR: max_obligations must be >= 1"
        );

        // Initialize: check if initial states satisfy safety
        match self.init_safe() {
            InitResult::Safe => {}
            InitResult::Unsafe => {
                if self.config.verbose {
                    safe_eprintln!("PDR: Initial state violates safety");
                }
                let cex = self.build_trivial_cex();
                // INVARIANT: Trivial CEX (init violates safety) has no transition
                // steps — the initial state directly violates the safety property.
                // Must be checked in release builds (#3095).
                assert!(
                    cex.steps.is_empty(),
                    "BUG: Trivial counterexample should have empty steps, got {}",
                    cex.steps.len()
                );
                return Some(self.finish_with_result_trace(PdrResult::Unsafe(cex)));
            }
        }

        // #6047: Acyclic safety check for problems with no transitions.
        // After inlining, model-checker-consumer-generated CHC problems often reduce to a single
        // predicate with only fact and query clauses (no self-loop transitions).
        // For such problems, `Inv = true` is trivially inductive (no transitions
        // to violate it). Safety reduces to checking each query constraint alone.
        //
        // Standard PDR fails here because:
        // 1. strengthen() finds no bad states (queries are independently Unsat)
        // 2. No lemmas are learned (no blocking needed)
        // 3. check_fixed_point rejects empty-frame equality
        // 4. check_invariants_prove_safety requires at least one lemma
        //
        // This check directly verifies each query constraint and returns Safe
        // with the trivial `true` model when all queries are contradictory.
        if self.problem.transitions().next().is_none() {
            if self.config.verbose {
                safe_eprintln!("PDR: No transition clauses — trying acyclic safety check");
            }
            if let Some(model) = self.try_acyclic_safety_proof() {
                return Some(self.finish_safe_with_result_trace(model, "acyclic safety proof"));
            }
        }

        // Cheap bug-finding precheck for tiny pure-LIA systems. PDR can spend a
        // long time generalizing shallow unsafe states before the must-reachability
        // summaries catch up. Bounded model checking is sound for positive
        // counterexamples and quickly discharges those cases without affecting
        // safety proofs.
        if let Some(result) = self.try_bmc_unsafe_precheck() {
            return Some(result);
        }

        // Initialize must-summaries at level 0 from fact clauses (Spacer technique)
        // For each predicate, add the initial constraints as must-reachable states
        if self.config.use_must_summaries || self.config.use_mixed_summaries {
            if !self.init_must_summaries_from_facts() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }
        }

        // Enrich must-summaries with self-loop closure states (#1613).
        // For phase-chain benchmarks (gj2007, s_mutants), the init must-summary cannot
        // satisfy inter-predicate transition guards. This adds exit guards as additional
        // must-summary disjuncts, enabling forward propagation through phase chains.
        self.enrich_must_summaries_with_loop_closure();

        // Propagate symbolic equality constraints (B = C) to derived predicates (#1613).
        // The forward must-summary propagation only propagates concrete points; this fills
        // the gap by propagating symbolic constraints that are preserved through transitions.
        // NOTE: Also called inside the startup fixpoint loop (#2248) to propagate equalities
        // discovered by discover_equality_invariants().
        self.propagate_symbolic_equalities_to_derived_predicates();

        // IMPORTANT: For predicates that are TRULY unreachable, frame[0] should be empty.
        // A predicate is truly unreachable if it has no fact clauses AND is not reachable
        // via transitions from predicates with facts. (#1419)
        //
        // Previously, we blocked ALL predicates without facts, which was overly conservative
        // for phase-chain benchmarks like gj2007_m_* where predicates are reachable via
        // transitions even though they lack direct init clauses.
        //
        // A lemma formula represents the invariant (NOT the blocking formula).
        // To block all states, we add lemma.formula = false, which means:
        // - The invariant is "false" (no states satisfy it)
        // - All states at level 0 are blocked for this predicate
        self.block_unreachable_predicates_at_frame0();

        // Run startup invariant discovery pipeline and direct safety check.
        // Returns Some(result) if solver should return early (discovery proved safety
        // or cancelled). See startup.rs for the full pipeline.
        if let Some(result) = self.run_startup_discovery() {
            return Some(result);
        }

        None
    }

    fn try_bmc_unsafe_precheck(&mut self) -> Option<PdrResult> {
        if !self.is_bmc_unsafe_precheck_candidate() {
            return None;
        }

        let max_depth = self.config.max_frames.clamp(1, 24);
        let mut config = crate::BmcConfig::with_engine_config(
            max_depth,
            false,
            self.config.cancellation_token.clone(),
        );
        config.per_depth_timeout = Some(std::time::Duration::from_millis(250));
        config.time_budget = Some(std::time::Duration::from_secs(2));

        if self.config.verbose {
            safe_eprintln!("PDR: Running bounded unsafe precheck to depth {max_depth}");
        }

        let solver = crate::BmcSolver::new(self.problem.clone(), config);
        match solver.solve() {
            PdrResult::Unsafe(cex) => {
                if self.config.verbose {
                    safe_eprintln!("PDR: Bounded unsafe precheck found counterexample");
                }
                Some(self.finish_with_result_trace(PdrResult::Unsafe(cex)))
            }
            _ => None,
        }
    }

    fn is_bmc_unsafe_precheck_candidate(&self) -> bool {
        if self.problem.has_bv_sorts()
            || self.problem.has_array_sorts()
            || self.problem.has_real_sorts()
            || self.problem.has_datatype_sorts()
        {
            return false;
        }

        if self.problem.predicates().len() > 2 || self.problem.clauses().len() > 8 {
            return false;
        }

        if self.problem.queries().next().is_none() || self.problem.transitions().next().is_none() {
            return false;
        }

        if !self.has_single_int_countdown_lower_query() {
            return false;
        }

        self.problem
            .predicates()
            .iter()
            .all(|pred| pred.arg_sorts.len() <= 4)
    }

    fn has_single_int_countdown_lower_query(&self) -> bool {
        let predicates = self.problem.predicates();
        if predicates.len() != 1 {
            return false;
        }
        let Some(predicate) = predicates.first() else {
            return false;
        };
        if !matches!(predicate.arg_sorts.as_slice(), [ChcSort::Int]) {
            return false;
        }
        let predicate_id = predicate.id;

        let has_countdown_transition = self.problem.transitions().any(|clause| {
            let [(body_pred, body_args)] = clause.body.predicates.as_slice() else {
                return false;
            };
            let crate::ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
                return false;
            };
            if body_pred != head_pred || body_args.len() != 1 || head_args.len() != 1 {
                return false;
            }
            let Some(body_var) = Self::int_var_name(&body_args[0]) else {
                return false;
            };
            Self::is_positive_decrement_of_var(&head_args[0], body_var)
        });

        has_countdown_transition
            && self.problem.queries().any(|clause| {
                let [(query_pred, query_args)] = clause.body.predicates.as_slice() else {
                    return false;
                };
                if query_args.len() != 1 {
                    return false;
                }
                let Some(query_var) = Self::int_var_name(&query_args[0]) else {
                    return false;
                };
                *query_pred == predicate_id
                    && clause
                        .body
                        .constraint
                        .as_ref()
                        .is_some_and(|constraint| Self::contains_lower_query(constraint, query_var))
            })
    }

    fn int_var_name(expr: &ChcExpr) -> Option<&str> {
        match expr {
            ChcExpr::Var(var) if matches!(&var.sort, ChcSort::Int) => Some(&var.name),
            _ => None,
        }
    }

    fn is_positive_decrement_of_var(expr: &ChcExpr, var_name: &str) -> bool {
        match expr {
            ChcExpr::Op(crate::ChcOp::Sub, args) if args.len() == 2 => {
                Self::is_bmc_precheck_var_named(args[0].as_ref(), var_name)
                    && matches!(args[1].as_ref(), ChcExpr::Int(delta) if *delta > 0)
            }
            ChcExpr::Op(crate::ChcOp::Add, args) if args.len() == 2 => {
                (Self::is_bmc_precheck_var_named(args[0].as_ref(), var_name)
                    && matches!(args[1].as_ref(), ChcExpr::Int(delta) if *delta < 0))
                    || (Self::is_bmc_precheck_var_named(args[1].as_ref(), var_name)
                        && matches!(args[0].as_ref(), ChcExpr::Int(delta) if *delta < 0))
            }
            _ => false,
        }
    }

    fn contains_lower_query(expr: &ChcExpr, var_name: &str) -> bool {
        match expr {
            ChcExpr::Op(crate::ChcOp::And, args) => args
                .iter()
                .any(|arg| Self::contains_lower_query(arg, var_name)),
            ChcExpr::Op(crate::ChcOp::Lt | crate::ChcOp::Le, args) if args.len() == 2 => {
                Self::is_bmc_precheck_var_named(args[0].as_ref(), var_name)
                    && matches!(args[1].as_ref(), ChcExpr::Int(_))
            }
            ChcExpr::Op(crate::ChcOp::Gt | crate::ChcOp::Ge, args) if args.len() == 2 => {
                matches!(args[0].as_ref(), ChcExpr::Int(_))
                    && Self::is_bmc_precheck_var_named(args[1].as_ref(), var_name)
            }
            _ => false,
        }
    }

    fn is_bmc_precheck_var_named(expr: &ChcExpr, var_name: &str) -> bool {
        matches!(expr, ChcExpr::Var(var) if var.name == var_name)
    }

    /// Initialize must-summaries at level 0 from fact clauses.
    /// Returns `true` on success, `false` if reach-fact capacity was exceeded.
    fn init_must_summaries_from_facts(&mut self) -> bool {
        for (clause_index, clause) in self.problem.clauses().iter().enumerate() {
            // Fact clause: no body predicates, just a constraint leading to head
            if clause.body.predicates.is_empty() {
                if let crate::ClauseHead::Predicate(pred, head_args) = &clause.head {
                    // Get the constraint on initial state (if any)
                    let constraint = clause
                        .body
                        .constraint
                        .clone()
                        .unwrap_or(ChcExpr::Bool(true));

                    // Map clause variables to canonical predicate variables
                    if let Some(canonical_vars) = self.canonical_vars(*pred) {
                        if head_args.len() == canonical_vars.len() {
                            let rewritten = fact_summary::rewrite_fact_summary(
                                &constraint,
                                head_args,
                                canonical_vars,
                            );
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Init must-summary for pred {} at level 0: {}",
                                    pred.index(),
                                    rewritten
                                );
                            }
                            // Create ReachFact FIRST to get id for backed must-summary
                            let mut instances = FxHashMap::default();
                            cube::extract_equalities_from_formula(&rewritten, &mut instances);
                            let Some(id) = Self::insert_reach_fact_bounded(
                                &mut self.reachability,
                                self.config.verbose,
                                ReachFact {
                                    id: ReachFactId(0),
                                    predicate: *pred,
                                    level: 0,
                                    state: rewritten.clone(),
                                    incoming_clause: Some(clause_index),
                                    premises: Vec::new(),
                                    instances,
                                },
                            ) else {
                                // Capacity exceeded — abort gracefully (caller
                                // returns Unknown via the Option path).
                                return false;
                            };

                            // Add to must-summaries as BACKED (proven reachable via fact clause)
                            let added = self.reachability.must_summaries.add_backed(
                                0,
                                *pred,
                                rewritten.clone(),
                                id,
                            );
                            if added {
                                // Add to reach solver as BACKED entry for fast short-circuit
                                self.reachability
                                    .reach_solvers
                                    .add_backed(*pred, id, rewritten);
                            }
                        }
                    }
                }
            }
        }
        true
    }
}
