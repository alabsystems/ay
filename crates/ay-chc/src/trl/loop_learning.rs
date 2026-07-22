// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TRL loop handling, blocking clause computation, variable classification,
//! transitive projection, and versioning helpers.
//!
//! Extracted from `trl/mod.rs` as part of #4701 wave 2.

use super::*;

impl TrlSolver {
    // ---- Loop handling ----

    /// Handle loop detection: learn relation and add blocking clause.
    ///
    /// When a NEW relation is learned, the incremental solver is reset because
    /// step formulas (which are disjunctions over all learned relations) change.
    /// When a COVERING relation is used, only the blocking clause is added.
    pub(super) fn handle_loop(&mut self, start: usize, end: usize) -> bool {
        let loop_length = end - start + 1;

        // Specialize the loop range to a single composed transition.
        //
        // NOTE: We must compose multi-step loops by introducing intermediate state
        // vars; simply conjoining step formulas is unsound for length>1 loops.
        // (Re: #1514)
        let (loop_body, loop_model) = self.specialize(start, end, |v| self.is_temp_var(v));

        let mut newly_learned = false;
        let learned_id = match self.has_covering_relation(loop_length, &loop_model) {
            Some(covering_id) => {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "[TRL] Loop {}->{} covered by relation #{}, skipping learning",
                        start,
                        end,
                        covering_id
                    );
                }
                covering_id
            }
            None => match self.transitive_projection(&loop_body, &loop_model) {
                Some(tp) => {
                    let id = self.learned.len(); // will be at this index after push
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "[TRL] Learned relation #{id} from loop {start}->{end}: {tp}"
                        );
                    }
                    self.learned.push(tp);
                    newly_learned = true;
                    id
                }
                None => {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "[TRL] TRP could not learn a relation for loop {}->{}, returning Unknown",
                            start, end
                        );
                    }
                    return false;
                }
            },
        };

        // Add blocking clause
        let mut blocking = self.compute_blocking_clause(
            start,
            loop_length,
            learned_id,
            &self.learned[learned_id],
            &loop_model,
        );

        // For covered self-loops: block the model's state assignment to force a
        // genuinely different path. This replaces the old acceleration-only approach
        // (__trp_n > 2^streak) which caused self-loop starvation — the solver kept
        // finding the same loop with larger n but never explored different paths.
        // Analogous to Golem's neg(project(relation, model)).
        if loop_length == 1 && self.same_loop_streak > 1 {
            let model_block = self.build_model_blocking_clause(start, &loop_model);
            blocking = ChcExpr::and(blocking, model_block);
            if self.config.base.verbose {
                safe_eprintln!(
                    "[TRL] Model blocking at depth {} (streak={})",
                    start,
                    self.same_loop_streak
                );
            }
        }

        // Blocking clauses are indexed by the *state depth* (timestep) at which they apply.
        // A trace element index `end` corresponds to the transition from `end` to `end+1`,
        // so the clause must be active at depth `end+1` when unrolling.
        let depth_key = end + 1;

        if self.config.base.verbose {
            safe_eprintln!(
                "[TRL] Adding blocking clause for depth {}, learned_id {}",
                depth_key,
                learned_id
            );
        }

        self.blocked
            .entry(depth_key)
            .or_default()
            .insert(learned_id, blocking.clone());

        // Assert blocking clause into the incremental context for persistence.
        self.inc_smt
            .assert_permanent(&blocking, &mut self.smt_helper);

        // If a new relation was learned, step formulas change (they include a
        // disjunction over ALL learned relations). Reset the incremental solver
        // so extend_encoding re-encodes with the updated step formulas.
        if newly_learned {
            self.reset_incremental_solver();
        }

        true
    }

    /// Compute blocking clause per TRL paper.
    ///
    /// For self-loops (l=1): not(cvp) OR trace_id@start >= learned_id
    /// For multi-step loops: not(cvp)
    pub(super) fn compute_blocking_clause(
        &self,
        start: usize,
        length: usize,
        _learned_id: usize,
        learned_relation: &ChcExpr,
        loop_model: &FxHashMap<String, SmtValue>,
    ) -> ChcExpr {
        let state_vars = self.get_state_var_set();
        let cvp_result = cvp(learned_relation, loop_model, &state_vars);
        let negated_cvp = ChcExpr::not(self.version_expr(&cvp_result, start));

        if length == 1 {
            // For self-loops: not(cvp) OR trace_id@start >= 1.
            //
            // Any learned relation may replace the original step; the blocking
            // clause must not require reusing the specific `learned_id`.
            let trace_var = ChcVar::new("trace_id", ChcSort::Int);
            let trace_var_at = TransitionSystem::version_var(&trace_var, start);
            ChcExpr::or(
                negated_cvp,
                ChcExpr::ge(ChcExpr::var(trace_var_at), ChcExpr::int(1)),
            )
        } else {
            // For multi-step loops: just not(cvp)
            negated_cvp
        }
    }

    /// Check if any learned relation already covers this loop.
    pub(super) fn has_covering_relation(
        &self,
        loop_length: usize,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<usize> {
        // LoAT sets n=1 before evaluation (trputil.cpp:381-403). Since TRP now
        // keeps `__trp_n` as a free variable, we must provide a value for coverage
        // checking. n=1 is conservative: if the relation covers at n=1, it covers
        // for all n > 0.
        let mut extended_model: FxHashMap<String, SmtValue> = model.clone();
        if !extended_model.contains_key(TRP_N_VAR_NAME) {
            extended_model.insert(TRP_N_VAR_NAME.to_string(), SmtValue::Int(1));
        }

        // LoAT skips original clauses for self-loops (trputil.cpp:391-393).
        // In AY, id 0 is the original transition.
        for (id, rel) in self.learned.iter().enumerate().rev() {
            if loop_length == 1 && id == 0 {
                continue;
            }
            if self.mbp.eval_bool(rel, &extended_model) == Some(true) {
                return Some(id);
            }
        }
        None
    }

    // ---- Variable classification ----

    /// Return true if `v` is a state variable (pre-state form).
    fn is_state_pre_var(&self, v: &ChcVar) -> bool {
        self.ts.vars.iter().any(|sv| sv.name == v.name)
    }

    /// Return true if `v` is a state variable (post-state form, `_next` suffix).
    fn is_state_post_var(&self, v: &ChcVar) -> bool {
        let Some(base) = v.name.strip_suffix("_next") else {
            return false;
        };
        self.ts.vars.iter().any(|sv| sv.name == base)
    }

    /// Return true if `v` is not a state var (pre/post), i.e. a temporary.
    ///
    /// This matches LoAT's notion of "temp vars": anything outside the program's
    /// pre/post state variable sets (e.g., `trace_id`, chaining intermediates,
    /// MBP auxiliaries, etc.).
    pub(super) fn is_temp_var(&self, v: &ChcVar) -> bool {
        !self.is_state_pre_var(v) && !self.is_state_post_var(v)
    }

    /// Get the implicant cube formula for a trace step.
    pub(super) fn get_implicant_for_step(&self, step: usize) -> Option<ChcExpr> {
        let elem = self.trace.elements.get(step)?;
        self.trace.graph.get_expr(elem.implicant_id).cloned()
    }

    // ---- Transitive projection ----

    /// Compute transitive projection using recurrence analysis.
    ///
    /// This is the core learning mechanism. TRP combines MBP with recurrence
    /// analysis to compute formulas that summarize multiple loop iterations.
    ///
    /// Implements #1176.
    fn transitive_projection(
        &self,
        loop_body: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        // Use TRP to compute transitive projection
        self.trp.compute(loop_body, model)
    }

    // ---- Versioning ----

    /// Version an expression for timestep k.
    pub(super) fn version_expr(&self, expr: &ChcExpr, k: usize) -> ChcExpr {
        TransitionSystem::version_expr(expr, &self.ts.vars, k)
    }

    /// Version a transition formula from time `from` to time `to`.
    pub(super) fn version_transition(&self, trans: &ChcExpr, from: usize, to: usize) -> ChcExpr {
        let mut substitutions: Vec<(ChcVar, ChcExpr)> = Vec::new();

        // State vars at `from`
        for v in &self.ts.vars {
            substitutions.push((
                v.clone(),
                ChcExpr::var(TransitionSystem::version_var(v, from)),
            ));
        }

        // TRL trace var is a pre-state "choice" variable, so it versions at `from`
        let trace_var = ChcVar::new("trace_id", ChcSort::Int);
        substitutions.push((
            trace_var.clone(),
            ChcExpr::var(TransitionSystem::version_var(&trace_var, from)),
        ));

        // Version __trp_n per step so each transition step can choose its own
        // iteration count independently (Golem TRL.cc:95-100).
        let n_var = ChcVar::new(TRP_N_VAR_NAME, ChcSort::Int);
        substitutions.push((
            n_var.clone(),
            ChcExpr::var(TransitionSystem::version_var(&n_var, from)),
        ));

        // _next vars at `to`
        for v in &self.ts.vars {
            let next_var = ChcVar::new(format!("{}_next", v.name), v.sort.clone());
            substitutions.push((next_var, ChcExpr::var(TransitionSystem::version_var(v, to))));
        }

        trans.substitute(&substitutions)
    }
}
