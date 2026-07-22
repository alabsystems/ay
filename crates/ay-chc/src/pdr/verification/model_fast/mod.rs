// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fast deadline-bounded model verification for PDR solver.
//!
//! Extracted from model.rs — the `verify_model_fast` method uses shorter
//! per-clause SMT timeouts and bails out early when a deadline is exceeded.
//! Used by `check_invariants_prove_safety` where spending 8s on verify_model
//! would exhaust the portfolio budget before the engine can report Safe.

use super::*;

impl PdrSolver {
    pub(super) fn fixed_int_subst_from_conjuncts(expr: &ChcExpr) -> Vec<(ChcVar, ChcExpr)> {
        #[derive(Clone, Copy, Debug, Default)]
        struct IntBounds {
            lower: Option<i128>,
            upper: Option<i128>,
        }

        fn update_lower(bounds: &mut IntBounds, new_lower: i128) {
            bounds.lower = Some(match bounds.lower {
                Some(existing) => existing.max(new_lower),
                None => new_lower,
            });
        }

        fn update_upper(bounds: &mut IntBounds, new_upper: i128) {
            bounds.upper = Some(match bounds.upper {
                Some(existing) => existing.min(new_upper),
                None => new_upper,
            });
        }

        fn update_eq(bounds: &mut IntBounds, value: i128) {
            update_lower(bounds, value);
            update_upper(bounds, value);
        }

        /// No stack guard needed: only recurses through And (flattened, depth <= 3).
        fn collect(expr: &ChcExpr, bounds: &mut FxHashMap<ChcVar, IntBounds>) {
            match expr {
                ChcExpr::Op(ChcOp::And, args) => {
                    for arg in args {
                        collect(arg.as_ref(), bounds);
                    }
                }
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(k)) | (ChcExpr::Int(k), ChcExpr::Var(v))
                            if v.sort == ChcSort::Int =>
                        {
                            update_eq(bounds.entry(v.clone()).or_default(), *k);
                        }
                        _ => {}
                    }
                }
                ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt, args)
                    if args.len() == 2 =>
                {
                    let op = match expr {
                        ChcExpr::Op(op, _) => op,
                        _ => return, // #6091: defensive
                    };
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(k)) if v.sort == ChcSort::Int => {
                            let b = bounds.entry(v.clone()).or_default();
                            match op {
                                ChcOp::Le => update_upper(b, *k),
                                ChcOp::Lt => update_upper(b, k.saturating_sub(1)),
                                ChcOp::Ge => update_lower(b, *k),
                                ChcOp::Gt => update_lower(b, k.saturating_add(1)),
                                _ => {}
                            }
                        }
                        (ChcExpr::Int(k), ChcExpr::Var(v)) if v.sort == ChcSort::Int => {
                            let b = bounds.entry(v.clone()).or_default();
                            match op {
                                ChcOp::Le => update_lower(b, *k),
                                ChcOp::Lt => update_lower(b, k.saturating_add(1)),
                                ChcOp::Ge => update_upper(b, *k),
                                ChcOp::Gt => update_upper(b, k.saturating_sub(1)),
                                _ => {}
                            }
                        }
                        _ => {}
                    }
                }
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
                    // ¬(x < k)  ==>  x >= k
                    ChcExpr::Op(ChcOp::Lt, inner) if inner.len() == 2 => {
                        if let (ChcExpr::Var(v), ChcExpr::Int(k)) =
                            (inner[0].as_ref(), inner[1].as_ref())
                        {
                            if v.sort == ChcSort::Int {
                                update_lower(bounds.entry(v.clone()).or_default(), *k);
                            }
                        }
                    }
                    // ¬(x <= k)  ==>  x > k  ==>  x >= k+1
                    ChcExpr::Op(ChcOp::Le, inner) if inner.len() == 2 => {
                        if let (ChcExpr::Var(v), ChcExpr::Int(k)) =
                            (inner[0].as_ref(), inner[1].as_ref())
                        {
                            if v.sort == ChcSort::Int {
                                update_lower(
                                    bounds.entry(v.clone()).or_default(),
                                    k.saturating_add(1),
                                );
                            }
                        }
                    }
                    // ¬(x > k)  ==>  x <= k
                    ChcExpr::Op(ChcOp::Gt, inner) if inner.len() == 2 => {
                        if let (ChcExpr::Var(v), ChcExpr::Int(k)) =
                            (inner[0].as_ref(), inner[1].as_ref())
                        {
                            if v.sort == ChcSort::Int {
                                update_upper(bounds.entry(v.clone()).or_default(), *k);
                            }
                        }
                    }
                    // ¬(x >= k)  ==>  x < k  ==>  x <= k-1
                    ChcExpr::Op(ChcOp::Ge, inner) if inner.len() == 2 => {
                        if let (ChcExpr::Var(v), ChcExpr::Int(k)) =
                            (inner[0].as_ref(), inner[1].as_ref())
                        {
                            if v.sort == ChcSort::Int {
                                update_upper(
                                    bounds.entry(v.clone()).or_default(),
                                    k.saturating_sub(1),
                                );
                            }
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
        }

        let mut bounds: FxHashMap<ChcVar, IntBounds> = FxHashMap::default();
        collect(expr, &mut bounds);

        let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (var, b) in bounds {
            if let (Some(lower), Some(upper)) = (b.lower, b.upper) {
                if lower == upper {
                    subst.push((var, ChcExpr::Int(lower)));
                }
            }
        }
        subst
    }

    /// Fast verification with a wall-clock deadline.
    ///
    /// Uses shorter per-clause SMT timeouts and bails out early if the deadline
    /// is exceeded. Returns `true` only if all clauses verified within budget.
    /// Used by `check_invariants_prove_safety` where spending 8s on verify_model
    /// would exhaust the portfolio budget before the engine can report Safe.
    ///
    /// Part of #3121: reduce check_invariants startup overhead.
    pub(in crate::pdr) fn verify_model_fast(
        &mut self,
        model: &InvariantModel,
        deadline: ay_core::time::Instant,
    ) -> bool {
        self.telemetry.verification_queries = self.telemetry.verification_queries.saturating_add(1);

        // Use a tight per-clause timeout: 500ms initial, 2s retry (vs 2s/30s default).
        // This is aggressive but sufficient for most verification queries. If a clause
        // can't be verified quickly, the caller falls back to slower strategies.
        let fast_initial = std::time::Duration::from_millis(500);
        let fast_retry = std::time::Duration::from_secs(2);

        // SOUNDNESS: Interpretations with free (non-binder) variables cannot be
        // validated by substitution — same-named clause variables capture them,
        // turning clause checks into vacuous UNSAT queries (022c-horn_000).
        // Same check as verify_model_impl.
        if self.model_has_free_interpretation_vars(model) {
            return false;
        }

        // #5930: Reject models where predicates have Real-sorted args but the
        // model interpretation is Bool/Int-only. Same check as verify_model_impl.
        for pred in self.problem.predicates() {
            let has_real_args = pred.arg_sorts.iter().any(|s| matches!(s, ChcSort::Real));
            if !has_real_args {
                continue;
            }
            if let Some(interp) = model.get(&pred.id) {
                let has_real_in_formula = interp
                    .formula
                    .vars()
                    .iter()
                    .any(|v| v.sort == ChcSort::Real);
                if !has_real_in_formula {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model_fast: rejecting model — pred {} has Real args but \
                             model is Bool/Int-only (#5930)",
                            pred.id.index()
                        );
                    }
                    return false;
                }
            }
        }

        // #3215 soundness fix: track whether any transition clause used filtered invariant.
        // If so, we must re-verify query clauses with the same filtered invariant,
        // matching the #73 soundness fix in verify_model_with_cex.
        let mut used_filtered_invariant = false;
        let mut query_clause_info: Vec<QueryClauseInfo> = Vec::new();

        // #5653: Budget for concrete_transition_check to avoid cumulative overhead.
        // When budget is exhausted, trust the SMT result for remaining clauses.
        let concrete_budget = std::time::Duration::from_millis(200);
        let mut concrete_elapsed = std::time::Duration::ZERO;
        // #7410: Rate-limit concrete cross-checks to 1-in-100 UNSAT results.
        let mut concrete_unsat_count: u64 = 0;

        for (clause_idx, clause) in self.problem.clauses().iter().enumerate() {
            // #3225: Check cooperative cancellation between clauses.
            if self.is_cancelled() {
                return false;
            }
            // Deadline check between clauses
            if ay_core::time::Instant::now() >= deadline {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model_fast: deadline exceeded at clause {}",
                        clause_idx
                    );
                }
                return false;
            }

            let body = match self.clause_body_under_model(&clause.body, model) {
                Some(b) => b,
                None => return false,
            };
            let body = self.bound_int_vars(body);

            match &clause.head {
                crate::ClauseHead::False => {
                    // #3215: Store query clause info for re-verification if filtered invariant used.
                    let invariant_body = self
                        .extract_invariant_only_from_body(&clause.body, model)
                        .unwrap_or(ChcExpr::Bool(true));
                    let bad_state = clause
                        .body
                        .constraint
                        .clone()
                        .unwrap_or(ChcExpr::Bool(true));
                    let pred_info = clause
                        .body
                        .predicates
                        .first()
                        .map(|(pred, args)| (*pred, args.clone()));
                    query_clause_info.push((pred_info, invariant_body, bad_state));

                    // Query clause: check body is UNSAT
                    if cube::is_trivial_contradiction(&body) {
                        continue;
                    }
                    let split_surface = Self::has_verification_case_split_surface(&body);
                    let mut result = SmtResult::Unknown;
                    if split_surface
                        && !Self::contains_mod_or_div(&body)
                        && !body.contains_array_ops()
                    {
                        let remaining =
                            deadline.saturating_duration_since(ay_core::time::Instant::now());
                        let timeout = VERIFY_CASE_SPLIT_TIMEOUT.min(remaining);
                        result = Self::try_verification_case_split(
                            &mut self.smt,
                            self.config.verbose,
                            &body,
                            timeout,
                        );
                    }
                    if matches!(result, SmtResult::Unknown) {
                        self.smt.reset();
                        let remaining =
                            deadline.saturating_duration_since(ay_core::time::Instant::now());
                        let timeout = fast_initial.min(remaining);
                        result = self.smt.check_sat_with_timeout(&body, timeout);
                    }
                    if matches!(result, SmtResult::Unknown)
                        && !Self::contains_mod_or_div(&body)
                        && !body.contains_array_ops()
                    {
                        let remaining =
                            deadline.saturating_duration_since(ay_core::time::Instant::now());
                        let timeout = fast_retry.min(remaining);
                        if !timeout.is_zero() {
                            self.smt.reset();
                            result = self.smt.check_sat_with_timeout(&body, timeout);
                        }
                    }
                    match result {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            // #5803: Concrete cross-check on query clauses.
                            // A false-UNSAT here produces a false Safe — the most
                            // dangerous soundness failure.
                            // #7410: Rate-limit: first 10, then 1-in-100.
                            concrete_unsat_count += 1;
                            if concrete_elapsed < concrete_budget
                                && (concrete_unsat_count <= 10
                                    || concrete_unsat_count.is_multiple_of(100))
                            {
                                let check_start = ay_core::time::Instant::now();
                                if let Some(cex_model) =
                                    concrete::transition_check(&body, &ChcExpr::Bool(true), &body)
                                {
                                    tracing::warn!(
                                        clause_idx,
                                        ?cex_model,
                                        "verify_model_fast: query clause SMT said UNSAT but concrete check found SAT (#5803)"
                                    );
                                    return false;
                                }
                                concrete_elapsed += check_start.elapsed();
                            } else if concrete_elapsed >= concrete_budget {
                                tracing::warn!(
                                    clause_idx,
                                    ?concrete_elapsed,
                                    "trust-proof fallback: query clause concrete cross-check \
                                     skipped due to budget exhaustion — trusting SMT UNSAT"
                                );
                                if self.config.strict_proofs {
                                    tracing::warn!(
                                        clause_idx,
                                        "strict-proofs: rejecting model — query clause \
                                         concrete cross-check was skipped"
                                    );
                                    return false;
                                }
                            }
                            continue;
                        }
                        SmtResult::Unknown => {
                            // Try mod-free fragment with deadline-aware timeout
                            if Self::contains_mod_or_div(&body) {
                                let mod_free = mod_div::drop_mod_div_conjuncts(&body);
                                if mod_free != ChcExpr::Bool(true) {
                                    self.smt.reset();
                                    let remaining = deadline
                                        .saturating_duration_since(ay_core::time::Instant::now());
                                    let timeout = fast_retry.min(remaining);
                                    if !timeout.is_zero() {
                                        let r = self.smt.check_sat_with_timeout(&mod_free, timeout);
                                        if matches!(
                                            r,
                                            SmtResult::Unsat
                                                | SmtResult::UnsatWithCore(_)
                                                | SmtResult::UnsatWithFarkas(_)
                                        ) {
                                            continue;
                                        }
                                    }
                                }
                                // Mod-substitution fallback (#3211)
                                if let Some(subst_body) =
                                    mod_div::substitute_mod_equalities_in_body(&body)
                                {
                                    if matches!(subst_body, ChcExpr::Bool(false)) {
                                        continue;
                                    }
                                    let remaining = deadline
                                        .saturating_duration_since(ay_core::time::Instant::now());
                                    let timeout = fast_retry.min(remaining);
                                    if !timeout.is_zero() {
                                        self.smt.reset();
                                        let r =
                                            self.smt.check_sat_with_timeout(&subst_body, timeout);
                                        if matches!(
                                            r,
                                            SmtResult::Unsat
                                                | SmtResult::UnsatWithCore(_)
                                                | SmtResult::UnsatWithFarkas(_)
                                        ) {
                                            continue;
                                        }
                                    }
                                }
                            }
                            return false;
                        }
                        _ => return false,
                    }
                }
                crate::ClauseHead::Predicate(_, _) => {
                    // Transition clause: check body => head
                    let head = match self.clause_head_under_model(&clause.head, model) {
                        Some(h) => h,
                        None => return false,
                    };
                    let head = self.bound_int_vars(head);
                    let query =
                        self.bound_int_vars(ChcExpr::and(body.clone(), ChcExpr::not(head.clone())));

                    // Fast-path: syntactic contradiction implies UNSAT.
                    if cube::is_trivial_contradiction(&query) {
                        continue;
                    }

                    let split_surface = Self::has_verification_case_split_surface(&query);
                    let mut result = SmtResult::Unknown;
                    if split_surface
                        && !Self::contains_mod_or_div(&query)
                        && !query.contains_array_ops()
                    {
                        let remaining =
                            deadline.saturating_duration_since(ay_core::time::Instant::now());
                        let timeout = VERIFY_CASE_SPLIT_TIMEOUT.min(remaining);
                        result = Self::try_verification_case_split(
                            &mut self.smt,
                            self.config.verbose,
                            &query,
                            timeout,
                        );
                    }
                    if matches!(result, SmtResult::Unknown) {
                        self.smt.reset();
                        let remaining =
                            deadline.saturating_duration_since(ay_core::time::Instant::now());
                        let timeout = fast_initial.min(remaining);
                        result = self.smt.check_sat_with_timeout(&query, timeout);
                    }
                    if matches!(result, SmtResult::Unknown)
                        && !Self::contains_mod_or_div(&query)
                        && !query.contains_array_ops()
                    {
                        let remaining =
                            deadline.saturating_duration_since(ay_core::time::Instant::now());
                        let timeout = fast_retry.min(remaining);
                        if !timeout.is_zero() {
                            self.smt.reset();
                            result = self.smt.check_sat_with_timeout(&query, timeout);
                        }
                    }
                    match result {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            // #6787: Executor cross-check — budgeted (#5970 regression).
                            // Skip for small queries (<100 AST nodes) — false-UNSAT
                            // correlates with large formulas where incompleteness manifests.
                            {
                                let query_size = query.node_count(200);
                                if query_size >= 100
                                    && self.cross_check_budget > std::time::Duration::ZERO
                                {
                                    let cross_timeout = self
                                        .cross_check_budget
                                        .min(std::time::Duration::from_millis(500));
                                    let propagated = FxHashMap::default();
                                    let cross_start = ay_core::time::Instant::now();
                                    let cross_result = self.smt.check_sat_via_executor(
                                        &query,
                                        &propagated,
                                        cross_timeout,
                                    );
                                    self.cross_check_budget = self
                                        .cross_check_budget
                                        .saturating_sub(cross_start.elapsed());
                                    if matches!(cross_result, SmtResult::Sat(_)) {
                                        if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: verify_model_fast: clause {} CROSS-CHECK FAILED — \
                                                 SmtContext=UNSAT but Executor=SAT (#6787)",
                                                clause_idx
                                            );
                                        }
                                        tracing::warn!(
                                            clause_idx,
                                            "verify_model_fast: Executor cross-check detected false-UNSAT (#6787)"
                                        );
                                        return false;
                                    }
                                }
                            }
                            // SOUNDNESS FIX #5381: Concrete evaluation sanity check
                            // (mirrors the check in verify_model_impl).
                            // #5653: Budget-limited to avoid cumulative overhead when
                            // PDR repeatedly attempts model verification.
                            // #7410: Rate-limit: first 10, then 1-in-100.
                            concrete_unsat_count += 1;
                            if concrete_elapsed < concrete_budget
                                && (concrete_unsat_count <= 10
                                    || concrete_unsat_count.is_multiple_of(100))
                            {
                                let check_start = ay_core::time::Instant::now();
                                if let Some(cex_model) =
                                    concrete::transition_check(&body, &head, &query)
                                {
                                    tracing::warn!(
                                        clause_idx,
                                        ?cex_model,
                                        "verify_model_fast: SMT said UNSAT but concrete check found SAT"
                                    );
                                    return false;
                                }
                                concrete_elapsed += check_start.elapsed();
                            } else if concrete_elapsed >= concrete_budget {
                                tracing::warn!(
                                    clause_idx,
                                    ?concrete_elapsed,
                                    "trust-proof fallback: transition clause concrete cross-check \
                                     skipped due to budget exhaustion — trusting SMT UNSAT"
                                );
                                if self.config.strict_proofs {
                                    tracing::warn!(
                                        clause_idx,
                                        "strict-proofs: rejecting model — transition clause \
                                         concrete cross-check was skipped"
                                    );
                                    return false;
                                }
                            }
                            continue;
                        }
                        SmtResult::Sat(_) => {
                            // Try aggressive filtering fallback
                            let body_filtered = Self::filter_blocking_lemmas_aggressive(&body);
                            let head_filtered = Self::filter_blocking_lemmas(&head);
                            let query_filtered =
                                ChcExpr::and(body_filtered, ChcExpr::not(head_filtered));
                            self.smt.reset();
                            let remaining =
                                deadline.saturating_duration_since(ay_core::time::Instant::now());
                            let timeout = fast_initial.min(remaining);
                            match self.smt.check_sat_with_timeout(&query_filtered, timeout) {
                                SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_) => {
                                    // #3215: Mark that filtered invariant was used
                                    used_filtered_invariant = true;
                                    continue;
                                }
                                _ => return false,
                            }
                        }
                        SmtResult::Unknown => {
                            // Try fixed-int substitution first (eliminates mod/div cheaply)
                            let fixed_int_subst = Self::fixed_int_subst_from_conjuncts(&body);
                            if !fixed_int_subst.is_empty() {
                                let simplified =
                                    query.substitute(&fixed_int_subst).simplify_constants();
                                self.smt.reset();
                                let remaining = deadline
                                    .saturating_duration_since(ay_core::time::Instant::now());
                                let timeout = fast_initial.min(remaining);
                                if !timeout.is_zero() {
                                    match self.smt.check_sat_with_timeout(&simplified, timeout) {
                                        SmtResult::Unsat
                                        | SmtResult::UnsatWithCore(_)
                                        | SmtResult::UnsatWithFarkas(_) => continue,
                                        _ => {}
                                    }
                                }
                            }
                            // Try mod-free fragment with deadline-aware timeout
                            if Self::contains_mod_or_div(&query) {
                                let mod_free = mod_div::drop_mod_div_conjuncts(&query);
                                if mod_free != ChcExpr::Bool(true) {
                                    self.smt.reset();
                                    let remaining = deadline
                                        .saturating_duration_since(ay_core::time::Instant::now());
                                    let timeout = fast_retry.min(remaining);
                                    if !timeout.is_zero() {
                                        let r = self.smt.check_sat_with_timeout(&mod_free, timeout);
                                        if matches!(
                                            r,
                                            SmtResult::Unsat
                                                | SmtResult::UnsatWithCore(_)
                                                | SmtResult::UnsatWithFarkas(_)
                                        ) {
                                            continue;
                                        }
                                    }
                                }
                                // #7048: Full mod elimination before rejecting.
                                let mod_eliminated = query.eliminate_mod();
                                if mod_eliminated != query {
                                    self.smt.reset();
                                    let remaining = deadline
                                        .saturating_duration_since(ay_core::time::Instant::now());
                                    let timeout = fast_retry.min(remaining);
                                    if !timeout.is_zero() {
                                        let r = self
                                            .smt
                                            .check_sat_with_timeout(&mod_eliminated, timeout);
                                        if matches!(
                                            r,
                                            SmtResult::Unsat
                                                | SmtResult::UnsatWithCore(_)
                                                | SmtResult::UnsatWithFarkas(_)
                                        ) {
                                            if self.config.verbose {
                                                safe_eprintln!(
                                                    "PDR: verify_model_fast: clause {} passed via mod elimination (#7048)",
                                                    clause_idx
                                                );
                                            }
                                            continue;
                                        }
                                    }
                                }
                                // Mod/div transition clause not verified — reject model (#5510)
                                // Soundness: Unknown means we could NOT verify the invariant
                                // is preserved by this transition. The caller will fall through
                                // to slower verification strategies. Previously this was
                                // `continue` which silently skipped unverified transition
                                // clauses, enabling spurious Safe results.
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: verify_model_fast: clause {} rejected (mod/div Unknown)",
                                        clause_idx
                                    );
                                }
                                return false;
                            }
                            return false;
                        }
                    }
                }
            }
        }

        // #3215 soundness fix: re-verify query clauses with filtered invariant.
        // Mirrors the #73 soundness fix in verify_model_with_cex (lines 1402+).
        // If any transition clause was verified only via aggressive filtering,
        // the filtered invariant might admit bad states that the original blocking
        // lemmas excluded. We must check that filtered_invariant ∧ bad_state is UNSAT.
        if used_filtered_invariant && !query_clause_info.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: verify_model_fast: re-verifying {} query clauses with filtered invariant",
                    query_clause_info.len()
                );
            }
            for (i, (_pred_info, invariant_body, bad_state)) in query_clause_info.iter().enumerate()
            {
                // #3225: Check cooperative cancellation between re-verification queries.
                if self.is_cancelled() {
                    return false;
                }
                if ay_core::time::Instant::now() >= deadline {
                    return false;
                }
                let filtered_invariant = Self::filter_blocking_lemmas_aggressive(invariant_body);
                let query_body_filtered = ChcExpr::and(filtered_invariant, bad_state.clone());

                self.smt.reset();
                let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
                let timeout = fast_initial.min(remaining);
                match self
                    .smt
                    .check_sat_with_timeout(&query_body_filtered, timeout)
                {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: verify_model_fast: query {} passed filtered re-verification",
                                i
                            );
                        }
                    }
                    SmtResult::Unknown
                        if !Self::contains_mod_or_div(&query_body_filtered)
                            && !query_body_filtered.contains_array_ops() =>
                    {
                        // QF_LIA retry with extended timeout
                        let remaining =
                            deadline.saturating_duration_since(ay_core::time::Instant::now());
                        let timeout = fast_retry.min(remaining);
                        if timeout.is_zero() {
                            return false;
                        }
                        self.smt.reset();
                        match self
                            .smt
                            .check_sat_with_timeout(&query_body_filtered, timeout)
                        {
                            SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_) => {}
                            _ => return false,
                        }
                    }
                    _ => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: verify_model_fast: query {} FAILED filtered re-verification (soundness catch)",
                                i
                            );
                        }
                        return false;
                    }
                }
            }
        }

        true
    }
}

#[cfg(test)]
mod tests;
