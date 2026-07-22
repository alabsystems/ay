// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    // NOTE: `_try_prove_constant_int_under` and `try_prove_branch_constant_under_invariants`
    // were removed in #945. They incorrectly proved non-constant expressions as constant
    // because F1 invariants don't fully constrain all variables in the expression.
    // See: dillig12_m_e1 where (+ 2 D (* -2 E)) was incorrectly proved = 2.

    /// Find a definition for `var_name` inside a conjunction-shaped constraint.
    ///
    /// Returns the RHS expression if it finds a conjunct of the form:
    /// - `(= var_name expr)` or `(= expr var_name)`.
    fn find_var_definition_in_constraint(constraint: &ChcExpr, var_name: &str) -> Option<ChcExpr> {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => args
                .iter()
                .find_map(|a| Self::find_var_definition_in_constraint(a.as_ref(), var_name)),
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), rhs) if v.name == var_name => Some(rhs.clone()),
                    (lhs, ChcExpr::Var(v)) if v.name == var_name => Some(lhs.clone()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Attempt to prove that `expr` evaluates to a unique integer constant under `assumptions`.
    ///
    /// Uses a fresh variable and two SMT queries to avoid expression evaluation:
    /// 1. `assumptions ^ (__cc = expr)` -> SAT -> extract v = model(__cc)
    /// 2. `assumptions ^ (__cc = expr) ^ (__cc != v)` -> UNSAT confirms uniqueness
    ///
    /// Returns `Some(v)` if the expression is provably equal to the unique constant `v`
    /// under the assumptions; `None` otherwise.
    ///
    /// This is used for ITE branch constant proving where the branch expression may be
    /// non-syntactically-constant but provably constant under frame invariants.
    fn try_prove_unique_int_constant_under(
        &mut self,
        assumptions: &ChcExpr,
        expr: &ChcExpr,
        timeout: std::time::Duration,
    ) -> Option<i128> {
        // Create a fresh variable to capture the expression's value
        let fresh_var = ChcVar::new("__branch_const_cc".to_string(), ChcSort::Int);
        let fresh_var_expr = ChcExpr::var(fresh_var);

        // Query 1: Check if assumptions ^ (__cc = expr) is SAT and get a value
        let def_eq = ChcExpr::eq(fresh_var_expr.clone(), expr.clone());
        let query1 = ChcExpr::and(assumptions.clone(), def_eq);

        self.smt.reset();
        let result1 = self.smt.check_sat_with_timeout(&query1, timeout);

        let candidate_value = match result1 {
            SmtResult::Sat(model) => match model.get("__branch_const_cc") {
                Some(SmtValue::Int(v)) => *v,
                _ => return None,
            },
            _ => return None,
        };

        // Query 2: Check uniqueness - assumptions ^ (__cc = expr) ^ (__cc != candidate) should be UNSAT
        let not_candidate =
            ChcExpr::not(ChcExpr::eq(fresh_var_expr, ChcExpr::Int(candidate_value)));
        let query2 = ChcExpr::and(query1, not_candidate);

        self.smt.reset();
        let result2 = self.smt.check_sat_with_timeout(&query2, timeout);

        match result2 {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                Some(candidate_value)
            }
            _ => None,
        }
    }

    /// Discover constant values for predicates reachable via ITE transitions.
    ///
    /// When a transition clause has:
    /// - Body predicate with a constant argument (constrained at init)
    /// - Head arg that is an ITE depending on that constant
    /// - The constant value forces the ITE condition one way
    ///
    /// We can learn the resulting constant as an invariant for the head predicate.
    /// This is essential for benchmarks like dillig12_m where:
    /// - FUN has mode=0 constrained at init (5th arg)
    /// - FUN->SAD clause has `F = ite(C=1, complex_expr, 1)` where C is the mode
    /// - When mode=0, F=1 always, so we learn `SAD.arg0 = 1`
    pub(in crate::pdr::solver) fn discover_ite_constant_propagation(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Collect candidates: (head_pred, var_idx, constant_value)
        let mut candidates: Vec<(PredicateId, usize, i128)> = Vec::new();

        for head_pred in &predicates {
            let head_canonical = match self.canonical_vars(head_pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Check all transition clauses that define this predicate.
            let clauses: Vec<_> = self
                .problem
                .clauses_defining(head_pred.id)
                .cloned()
                .collect();
            for clause in &clauses {
                // Skip fact clauses
                if clause.body.predicates.is_empty() {
                    continue;
                }

                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => args,
                    crate::ClauseHead::False => continue,
                };

                // Get the body predicate and its args
                let (body_pred, body_args) = match clause.body.predicates.first() {
                    Some(p) => p,
                    None => continue,
                };

                // Get constant arguments for the body predicate
                let constant_args_set = self.detect_constant_arguments(*body_pred);
                if constant_args_set.is_empty() {
                    continue;
                }
                // Sort for deterministic iteration
                let mut constant_args: Vec<usize> = constant_args_set.into_iter().collect();
                constant_args.sort_unstable();

                // Get init values for body predicate to know which constants are constrained
                let body_init_values = self.get_init_values(*body_pred);

                // Check each head argument for ITE pattern
                for (head_idx, head_expr) in head_args.iter().enumerate() {
                    if head_idx >= head_canonical.len() {
                        continue;
                    }

                    // Some benchmarks introduce a temporary head variable and define it in the
                    // clause constraint (e.g., `F = ite(...)`) instead of placing the ITE
                    // directly in the predicate head arguments.
                    //
                    // If the head argument is a variable, try to inline its definition from the
                    // clause constraint so we can still propagate constants.
                    let mut head_expr = head_expr.clone();
                    if let ChcExpr::Var(v) = &head_expr {
                        if let Some(ref constraint) = clause.body.constraint {
                            if let Some(def) =
                                Self::find_var_definition_in_constraint(constraint, &v.name)
                            {
                                head_expr = def;
                            }
                        }
                    }

                    // Look for ITE expression
                    if let ChcExpr::Op(ChcOp::Ite, args) = &head_expr {
                        if args.len() != 3 {
                            continue;
                        }

                        let cond = &args[0];
                        let then_branch = &args[1];
                        let else_branch = &args[2];

                        // Extract constant from each branch (may be None for non-constant branches)
                        let then_const = Self::extract_constant(then_branch);
                        let else_const = Self::extract_constant(else_branch);

                        // We require at least one branch to be syntactically constant.
                        // Non-constant branch proving was removed in #945 due to soundness issues.

                        // Check if the condition depends on a constant body argument
                        let cond_vars = crate::expr_vars::expr_var_names(cond);

                        for const_arg_idx in &constant_args {
                            if *const_arg_idx >= body_args.len() {
                                continue;
                            }

                            // Check if this constant arg appears in the condition
                            let body_arg_var = match &body_args[*const_arg_idx] {
                                ChcExpr::Var(v) => v.name.clone(),
                                _ => continue,
                            };

                            if !cond_vars.contains(&body_arg_var) {
                                continue;
                            }

                            // Get the body predicate's canonical var name for this position
                            let body_canonical = match self.canonical_vars(*body_pred) {
                                Some(v) => v.to_vec(),
                                None => continue,
                            };

                            if *const_arg_idx >= body_canonical.len() {
                                continue;
                            }

                            let body_var_name = &body_canonical[*const_arg_idx].name;

                            // Check if we have an init value for this constant
                            if let Some(bounds) = body_init_values.get(body_var_name) {
                                if bounds.min != bounds.max {
                                    continue;
                                }

                                let const_val = bounds.min;

                                // Build substitution to evaluate the condition
                                let subst: Vec<(ChcVar, ChcExpr)> = vec![(
                                    ChcVar::new(body_arg_var.clone(), ChcSort::Int),
                                    ChcExpr::Int(const_val),
                                )];

                                let simplified_cond = cond.substitute(&subst).simplify_constants();

                                // Check if condition simplifies to a constant
                                match simplified_cond {
                                    ChcExpr::Bool(true) => {
                                        if let Some(result_const) = then_const {
                                            candidates.push((head_pred.id, head_idx, result_const));
                                            if self.config.verbose {
                                                safe_eprintln!(
                                                    "PDR: ITE constant propagation: pred {} arg {} = {} \
                                                     (cond {} with {}={} -> true -> {})",
                                                    head_pred.id.index(),
                                                    head_idx,
                                                    result_const,
                                                    cond,
                                                    body_arg_var,
                                                    const_val,
                                                    then_branch
                                                );
                                            }
                                        } else {
                                            let mode_binding = ChcExpr::eq(
                                                ChcExpr::Var(ChcVar::new(
                                                    body_arg_var.clone(),
                                                    ChcSort::Int,
                                                )),
                                                ChcExpr::Int(const_val),
                                            );
                                            let mut assumptions = mode_binding;

                                            if let Some(ref cc) = clause.body.constraint {
                                                assumptions = ChcExpr::and(assumptions, cc.clone());
                                            }

                                            if let Some(frame) =
                                                self.cumulative_frame_constraint(1, *body_pred)
                                            {
                                                if let Some(frame_on_body) = self
                                                    .apply_to_args(*body_pred, &frame, body_args)
                                                {
                                                    assumptions =
                                                        ChcExpr::and(assumptions, frame_on_body);
                                                }
                                            }

                                            if let Some(proven_const) = self
                                                .try_prove_unique_int_constant_under(
                                                    &assumptions,
                                                    then_branch,
                                                    std::time::Duration::from_millis(200),
                                                )
                                            {
                                                candidates.push((
                                                    head_pred.id,
                                                    head_idx,
                                                    proven_const,
                                                ));
                                                if self.config.verbose {
                                                    safe_eprintln!(
                                                        "PDR: ITE constant propagation (frame-proven): pred {} arg {} = {} \
                                                         (cond {} with {}={} -> true -> {} proven via invariants)",
                                                        head_pred.id.index(),
                                                        head_idx,
                                                        proven_const,
                                                        cond,
                                                        body_arg_var,
                                                        const_val,
                                                        then_branch
                                                    );
                                                }
                                            }
                                        }
                                    }
                                    ChcExpr::Bool(false) => {
                                        if let Some(result_const) = else_const {
                                            candidates.push((head_pred.id, head_idx, result_const));
                                            if self.config.verbose {
                                                safe_eprintln!(
                                                    "PDR: ITE constant propagation: pred {} arg {} = {} \
                                                     (cond {} with {}={} -> false -> {})",
                                                    head_pred.id.index(),
                                                    head_idx,
                                                    result_const,
                                                    cond,
                                                    body_arg_var,
                                                    const_val,
                                                    else_branch
                                                );
                                            }
                                        } else {
                                            let mode_binding = ChcExpr::eq(
                                                ChcExpr::Var(ChcVar::new(
                                                    body_arg_var.clone(),
                                                    ChcSort::Int,
                                                )),
                                                ChcExpr::Int(const_val),
                                            );
                                            let mut assumptions = mode_binding;

                                            if let Some(ref cc) = clause.body.constraint {
                                                assumptions = ChcExpr::and(assumptions, cc.clone());
                                            }

                                            if let Some(frame) =
                                                self.cumulative_frame_constraint(1, *body_pred)
                                            {
                                                if let Some(frame_on_body) = self
                                                    .apply_to_args(*body_pred, &frame, body_args)
                                                {
                                                    assumptions =
                                                        ChcExpr::and(assumptions, frame_on_body);
                                                }
                                            }

                                            if let Some(proven_const) = self
                                                .try_prove_unique_int_constant_under(
                                                    &assumptions,
                                                    else_branch,
                                                    std::time::Duration::from_millis(200),
                                                )
                                            {
                                                candidates.push((
                                                    head_pred.id,
                                                    head_idx,
                                                    proven_const,
                                                ));
                                                if self.config.verbose {
                                                    safe_eprintln!(
                                                        "PDR: ITE constant propagation (frame-proven): pred {} arg {} = {} \
                                                         (cond {} with {}={} -> false -> {} proven via invariants)",
                                                        head_pred.id.index(),
                                                        head_idx,
                                                        proven_const,
                                                        cond,
                                                        body_arg_var,
                                                        const_val,
                                                        else_branch
                                                    );
                                                }
                                            }
                                        }
                                    }
                                    _ => {
                                        let const_constraint = ChcExpr::eq(
                                            ChcExpr::Var(ChcVar::new(
                                                body_arg_var.clone(),
                                                ChcSort::Int,
                                            )),
                                            ChcExpr::Int(const_val),
                                        );

                                        // Check: const_constraint AND cond is UNSAT?
                                        let cond_true_query = ChcExpr::and(
                                            const_constraint.clone(),
                                            cond.as_ref().clone(),
                                        );
                                        self.smt.reset();
                                        match self.smt.check_sat_with_timeout(
                                            &cond_true_query,
                                            std::time::Duration::from_millis(200),
                                        ) {
                                            SmtResult::Unsat
                                            | SmtResult::UnsatWithCore(_)
                                            | SmtResult::UnsatWithFarkas(_) => {
                                                if let Some(result_const) = else_const {
                                                    candidates.push((
                                                        head_pred.id,
                                                        head_idx,
                                                        result_const,
                                                    ));
                                                    if self.config.verbose {
                                                        safe_eprintln!(
                                                            "PDR: ITE constant propagation (SMT): pred {} arg {} = {} \
                                                             (cond {} always false when {}={})",
                                                            head_pred.id.index(),
                                                            head_idx,
                                                            result_const,
                                                            cond,
                                                            body_arg_var,
                                                            const_val
                                                        );
                                                    }
                                                } else {
                                                    let mut assumptions = const_constraint.clone();
                                                    if let Some(ref cc) = clause.body.constraint {
                                                        assumptions =
                                                            ChcExpr::and(assumptions, cc.clone());
                                                    }
                                                    if let Some(frame) = self
                                                        .cumulative_frame_constraint(1, *body_pred)
                                                    {
                                                        if let Some(frame_on_body) = self
                                                            .apply_to_args(
                                                                *body_pred, &frame, body_args,
                                                            )
                                                        {
                                                            assumptions = ChcExpr::and(
                                                                assumptions,
                                                                frame_on_body,
                                                            );
                                                        }
                                                    }
                                                    if let Some(proven_const) = self
                                                        .try_prove_unique_int_constant_under(
                                                            &assumptions,
                                                            else_branch,
                                                            std::time::Duration::from_millis(200),
                                                        )
                                                    {
                                                        candidates.push((
                                                            head_pred.id,
                                                            head_idx,
                                                            proven_const,
                                                        ));
                                                        if self.config.verbose {
                                                            safe_eprintln!(
                                                                "PDR: ITE constant propagation (SMT+frame): pred {} arg {} = {} \
                                                                 (else_branch {} proven via invariants)",
                                                                head_pred.id.index(),
                                                                head_idx,
                                                                proven_const,
                                                                else_branch
                                                            );
                                                        }
                                                    }
                                                }
                                            }
                                            SmtResult::Sat(_) => {
                                                let cond_false_query = ChcExpr::and(
                                                    const_constraint.clone(),
                                                    ChcExpr::not(cond.as_ref().clone()),
                                                );
                                                self.smt.reset();
                                                match self.smt.check_sat_with_timeout(
                                                    &cond_false_query,
                                                    std::time::Duration::from_millis(200),
                                                ) {
                                                    SmtResult::Unsat
                                                    | SmtResult::UnsatWithCore(_)
                                                    | SmtResult::UnsatWithFarkas(_) => {
                                                        if let Some(result_const) = then_const {
                                                            candidates.push((
                                                                head_pred.id,
                                                                head_idx,
                                                                result_const,
                                                            ));
                                                            if self.config.verbose {
                                                                safe_eprintln!(
                                                                    "PDR: ITE constant propagation (SMT): pred {} arg {} = {} \
                                                                     (cond {} always true when {}={})",
                                                                    head_pred.id.index(),
                                                                    head_idx,
                                                                    result_const,
                                                                    cond,
                                                                    body_arg_var,
                                                                    const_val
                                                                );
                                                            }
                                                        } else {
                                                            let mut assumptions =
                                                                const_constraint.clone();
                                                            if let Some(ref cc) =
                                                                clause.body.constraint
                                                            {
                                                                assumptions = ChcExpr::and(
                                                                    assumptions,
                                                                    cc.clone(),
                                                                );
                                                            }
                                                            if let Some(frame) = self
                                                                .cumulative_frame_constraint(
                                                                    1, *body_pred,
                                                                )
                                                            {
                                                                if let Some(frame_on_body) = self
                                                                    .apply_to_args(
                                                                        *body_pred, &frame,
                                                                        body_args,
                                                                    )
                                                                {
                                                                    assumptions = ChcExpr::and(
                                                                        assumptions,
                                                                        frame_on_body,
                                                                    );
                                                                }
                                                            }
                                                            if let Some(proven_const) = self.try_prove_unique_int_constant_under(
                                                                &assumptions,
                                                                then_branch,
                                                                std::time::Duration::from_millis(200),
                                                            ) {
                                                                candidates.push((head_pred.id, head_idx, proven_const));
                                                                if self.config.verbose {
                                                                    safe_eprintln!(
                                                                        "PDR: ITE constant propagation (SMT+frame): pred {} arg {} = {} \
                                                                         (then_branch {} proven via invariants)",
                                                                        head_pred.id.index(),
                                                                        head_idx,
                                                                        proven_const,
                                                                        then_branch
                                                                    );
                                                                }
                                                            }
                                                        }
                                                    }
                                                    _ => {}
                                                }
                                            }
                                            SmtResult::Unknown => {}
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Deduplicate and add invariants
        candidates.sort_by_key(|(pid, idx, val)| (pid.index(), *idx, *val));
        candidates.dedup();

        for (pred_id, var_idx, const_val) in candidates {
            let canonical_vars = match self.canonical_vars(pred_id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if var_idx >= canonical_vars.len() {
                continue;
            }

            let var = &canonical_vars[var_idx];

            // Create equality invariant: var = const_val
            let eq_invariant = ChcExpr::eq(ChcExpr::var(var.clone()), ChcExpr::Int(const_val));

            // Check if already known
            let already_known = self.frames.len() > 1
                && self.frames[1]
                    .lemmas
                    .iter()
                    .any(|l| l.predicate == pred_id && l.formula == eq_invariant);

            if !already_known {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Discovered ITE constant propagation invariant for pred {}: {} = {}",
                        pred_id.index(),
                        var.name,
                        const_val
                    );
                }
                self.add_discovered_invariant(pred_id, eq_invariant, 1);
            }
        }
    }
}
