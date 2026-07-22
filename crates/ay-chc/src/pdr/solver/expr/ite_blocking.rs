// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ITE condition extraction, variable collection, and ITE blocking from counterexamples.

use super::super::PdrSolver;
use crate::pdr::counterexample::Counterexample;
use crate::pdr::frame::Lemma;
use crate::smt::{SmtResult, SmtValue};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

impl PdrSolver {
    /// Extract ITE conditions from an expression.
    pub(in crate::pdr::solver) fn extract_ite_conditions(
        expr: &ChcExpr,
        conditions: &mut Vec<ChcExpr>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::Ite, args) if !args.is_empty() => {
                conditions.push(args[0].as_ref().clone());
                // Recurse into then/else branches
                if args.len() >= 2 {
                    Self::extract_ite_conditions(&args[1], conditions);
                }
                if args.len() >= 3 {
                    Self::extract_ite_conditions(&args[2], conditions);
                }
            }
            ChcExpr::Op(_, args) => {
                for arg in args {
                    Self::extract_ite_conditions(arg, conditions);
                }
            }
            _ => {}
        }
    }

    /// Try to learn ITE-aware blocking lemmas from a spurious counterexample.
    ///
    /// When a CEX is spurious because an ITE expression was evaluated incorrectly,
    /// this function extracts the ITE conditions and learns blocking lemmas that
    /// prevent the same spurious path.
    ///
    /// Returns true if any new lemma was learned.
    pub(in crate::pdr::solver) fn try_learn_ite_blocking_from_cex(
        &mut self,
        cex: &Counterexample,
    ) -> bool {
        let witness = match &cex.witness {
            Some(w) => w,
            None => return false,
        };

        // Collect all potential candidates first (to avoid borrow conflicts)
        struct IteCandidate {
            body_pred: PredicateId,
            canonical_cond: ChcExpr,
            fact_constraint: ChcExpr,
            head_args: Vec<ChcExpr>,
            canonical_vars: Vec<ChcVar>,
        }

        // Grounded invariants from model-based case analysis
        struct GroundedInvariant {
            pred: PredicateId,
            formula: ChcExpr,
        }

        let mut candidates: Vec<IteCandidate> = Vec::new();
        let mut grounded_invariants: Vec<GroundedInvariant> = Vec::new();

        // Examine each entry in the witness to find ITE conditions
        for entry in &witness.entries {
            let clause_idx = match entry.incoming_clause {
                Some(idx) => idx,
                None => continue,
            };

            let clause = match self.problem.clauses().get(clause_idx) {
                Some(c) => c.clone(),
                None => continue,
            };

            // Extract ITE conditions from clause constraint
            let constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            let mut ite_conditions = Vec::new();
            Self::extract_ite_conditions(&constraint, &mut ite_conditions);

            // Also extract from head args (ITE can appear in computed values)
            if let crate::ClauseHead::Predicate(_, head_args) = &clause.head {
                for arg in head_args {
                    Self::extract_ite_conditions(arg, &mut ite_conditions);
                }
            }

            if ite_conditions.is_empty() {
                continue;
            }

            // Build model from entry instances
            let model: FxHashMap<String, SmtValue> = entry.instances.clone();

            // For each ITE condition, collect candidate info
            for ite_cond in &ite_conditions {
                // Try to evaluate the condition with the model
                let cond_value = crate::expr::evaluate_expr(ite_cond, &model);

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: ITE blocking - condition {} evaluated to {:?}",
                        ite_cond,
                        cond_value
                    );
                }

                // Get the source predicate (from clause body)
                let body_pred = match clause.body.predicates.first() {
                    Some((p, _)) => *p,
                    None => continue,
                };

                // Detect constant arguments for this predicate
                // This helps identify when ITE conditions depend on constant-but-unconstrained vars
                let constant_args_set = self.detect_constant_arguments(body_pred);
                // Sort for deterministic iteration
                let mut constant_args: Vec<usize> = constant_args_set.iter().copied().collect();
                constant_args.sort_unstable();

                // Get canonical vars (clone to avoid borrow conflict)
                let canonical_vars = match self.canonical_vars(body_pred) {
                    Some(v) => v.to_vec(),
                    None => continue,
                };

                // Check if the ITE condition depends on a constant argument
                // If so, and init doesn't constrain it, we need case-split
                let cond_vars = crate::expr_vars::expr_var_names(ite_cond);
                let depends_on_constant = !constant_args.is_empty()
                    && clause
                        .body
                        .predicates
                        .first()
                        .is_some_and(|(_, body_args)| {
                            body_args.iter().enumerate().any(|(idx, arg)| {
                                constant_args_set.contains(&idx)
                                    && match arg {
                                        ChcExpr::Var(v) => cond_vars.contains(&v.name),
                                        _ => false,
                                    }
                            })
                        });

                if self.config.verbose && depends_on_constant {
                    safe_eprintln!(
                        "PDR: ITE condition {} depends on constant argument (needs case-split)",
                        ite_cond
                    );
                }

                // Model-based grounding: When ITE depends on constant parameter,
                // extract the constant's value from the model and learn grounded constraints.
                // This follows Z3 Spacer's MBC algorithm (spacer_mbc.cpp).
                if depends_on_constant {
                    if let Some(cond_result) = cond_value {
                        // Find which constant arg appears in the condition and get its model value
                        let body_args_clone: Vec<ChcExpr> = clause
                            .body
                            .predicates
                            .first()
                            .map(|(_, args)| args.clone())
                            .unwrap_or_default();

                        for const_idx in &constant_args {
                            if *const_idx >= body_args_clone.len()
                                || *const_idx >= canonical_vars.len()
                            {
                                continue;
                            }

                            // Get the variable name used in the clause
                            let clause_var_name = match &body_args_clone[*const_idx] {
                                ChcExpr::Var(v) => v.name.clone(),
                                _ => continue,
                            };

                            // Check if this variable appears in the condition
                            if !cond_vars.contains(&clause_var_name) {
                                continue;
                            }

                            // Get model value for this constant
                            if let Some(model_val) = model.get(&clause_var_name) {
                                let const_int_val = match model_val {
                                    SmtValue::Int(n) => *n,
                                    _ => continue,
                                };

                                // Build a grounded blocking constraint:
                                // If the condition was true in the model, learn that when
                                // the constant equals this value, the condition must be true.
                                // This creates a case-specific invariant.
                                let canon_const = &canonical_vars[*const_idx];

                                // Ground the condition with ALL model values (not just constant)
                                // This makes the condition fully concrete
                                let mut full_subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
                                for (var_name, val) in &model {
                                    let var = ChcVar::new(var_name.clone(), ChcSort::Int);
                                    let expr = match val {
                                        SmtValue::Int(n) => ChcExpr::Int(*n),
                                        SmtValue::Bool(b) => ChcExpr::Bool(*b),
                                        _ => continue,
                                    };
                                    full_subst.push((var, expr));
                                }
                                let grounded_cond = ite_cond.substitute(&full_subst);

                                // Simplify - should now be a concrete Bool
                                let simplified_cond = grounded_cond.simplify_constants();

                                // The grounded condition should evaluate to a concrete boolean
                                if let ChcExpr::Bool(ground_truth) = simplified_cond {
                                    let cond_bool = match cond_result {
                                        SmtValue::Bool(b) => b,
                                        _ => continue,
                                    };
                                    if ground_truth == cond_bool {
                                        // Model is consistent, create invariant:
                                        // When canonical_const = const_int_val, the ITE evaluates
                                        // to ground_truth. This means we can learn:
                                        // (canonical_const = const_int_val) => canonical_cond is ground_truth
                                        //
                                        // For blocking, we want states where this implication is violated.
                                        // But simpler: just add the grounded condition as a lemma guard.

                                        // Actually, the simpler approach: learn a conditional lemma
                                        // that guards subsequent blocking with the constant's value.
                                        // For now, store this information for the candidate processing.

                                        if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: Model-based grounding - const {}={} makes condition {} = {}",
                                                canon_const.name, const_int_val, ite_cond, ground_truth
                                            );
                                        }

                                        // Create the grounded invariant:
                                        // (const = val) => (cond = ground_truth)
                                        // Rewritten: NOT(const = val) OR (cond if true, NOT cond if false)
                                        let const_eq = ChcExpr::eq(
                                            ChcExpr::var(canon_const.clone()),
                                            ChcExpr::Int(const_int_val),
                                        );

                                        // Map ITE condition to canonical variables
                                        let mut cond_subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
                                        for (arg, canon) in
                                            body_args_clone.iter().zip(canonical_vars.iter())
                                        {
                                            if let ChcExpr::Var(v) = arg {
                                                cond_subst
                                                    .push((v.clone(), ChcExpr::var(canon.clone())));
                                            }
                                        }
                                        let canonical_cond_expr = ite_cond.substitute(&cond_subst);

                                        let cond_part = if cond_bool {
                                            canonical_cond_expr.clone()
                                        } else {
                                            ChcExpr::not(canonical_cond_expr.clone())
                                        };

                                        let grounded_invariant =
                                            ChcExpr::or(ChcExpr::not(const_eq), cond_part);

                                        // Store for later processing
                                        grounded_invariants.push(GroundedInvariant {
                                            pred: body_pred,
                                            formula: grounded_invariant,
                                        });
                                    }
                                }
                            }
                        }
                    }
                }

                // Map the ITE condition to canonical variables
                let body_args: Vec<ChcExpr> = clause
                    .body
                    .predicates
                    .first()
                    .map(|(_, args)| args.clone())
                    .unwrap_or_default();

                if body_args.len() != canonical_vars.len() {
                    continue;
                }

                // Build substitution from body args to canonical vars
                let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
                for (arg, canon) in body_args.iter().zip(canonical_vars.iter()) {
                    if let ChcExpr::Var(v) = arg {
                        subst.push((v.clone(), ChcExpr::var(canon.clone())));
                    }
                }

                let canonical_cond = ite_cond.substitute(&subst);

                // Collect facts for this predicate
                for fact in self
                    .problem
                    .facts()
                    .filter(|f| f.head.predicate_id() == Some(body_pred))
                {
                    let fact_constraint =
                        fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                    let head_args = match &fact.head {
                        crate::ClauseHead::Predicate(_, args) => args.clone(),
                        crate::ClauseHead::False => continue,
                    };

                    if head_args.len() != canonical_vars.len() {
                        continue;
                    }

                    candidates.push(IteCandidate {
                        body_pred,
                        canonical_cond: canonical_cond.clone(),
                        fact_constraint,
                        head_args,
                        canonical_vars: canonical_vars.clone(),
                    });
                }
            }
        }

        // Now process candidates without borrow conflicts
        let mut learned = false;

        for candidate in candidates {
            // Substitute head args into the condition
            let mut arg_subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
            for (canon, head_arg) in candidate
                .canonical_vars
                .iter()
                .zip(candidate.head_args.iter())
            {
                arg_subst.push((canon.clone(), head_arg.clone()));
            }
            let cond_on_init = candidate.canonical_cond.substitute(&arg_subst);

            // Check if init => cond (the condition must be true at init)
            let cond_check = ChcExpr::and(
                candidate.fact_constraint.clone(),
                ChcExpr::not(cond_on_init.clone()),
            );
            // #7984: Use persistent executor backend for integer arithmetic.
            match self.check_sat_via_executor_backend(&cond_check) {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // Init implies this ITE condition is always true
                    // Learn this as an invariant if inductive
                    if !self
                        .frames
                        .iter()
                        .any(|f| f.contains_lemma(candidate.body_pred, &candidate.canonical_cond))
                    {
                        let blocking = ChcExpr::not(candidate.canonical_cond.clone());
                        // BUG FIX #685: Check both 1-step and self-inductiveness
                        if self.is_inductive_blocking(&blocking, candidate.body_pred, 0)
                            && self.is_self_inductive_blocking(&blocking, candidate.body_pred)
                        {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Learned ITE invariant for pred {}: {}",
                                    candidate.body_pred.index(),
                                    candidate.canonical_cond
                                );
                            }
                            self.add_lemma_to_frame(
                                Lemma::new(
                                    candidate.body_pred,
                                    candidate.canonical_cond.clone(),
                                    0,
                                ),
                                0,
                            );
                            learned = true;
                        }
                    }
                }
                SmtResult::Sat(_) => {
                    // Init doesn't imply the condition, check negation
                    let neg_cond = ChcExpr::not(cond_on_init);
                    let neg_cond_check = ChcExpr::and(candidate.fact_constraint.clone(), neg_cond);
                    // #7984: Use persistent executor backend for integer arithmetic.
                    match self.check_sat_via_executor_backend(&neg_cond_check) {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            // Init implies the condition is always false
                            // Learn NOT condition as invariant
                            let neg_canonical = ChcExpr::not(candidate.canonical_cond.clone());
                            if !self
                                .frames
                                .iter()
                                .any(|f| f.contains_lemma(candidate.body_pred, &neg_canonical))
                            {
                                let blocking = candidate.canonical_cond.clone();
                                // BUG FIX #685: Check both 1-step and self-inductiveness
                                if self.is_inductive_blocking(&blocking, candidate.body_pred, 0)
                                    && self
                                        .is_self_inductive_blocking(&blocking, candidate.body_pred)
                                {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: Learned ITE invariant (negated) for pred {}: {}",
                                            candidate.body_pred.index(),
                                            neg_canonical
                                        );
                                    }
                                    self.add_lemma_to_frame(
                                        Lemma::new(candidate.body_pred, neg_canonical, 0),
                                        0,
                                    );
                                    learned = true;
                                }
                            }
                        }
                        _ => {
                            // Init allows both true and false for the ITE condition.
                            // This is the parametric constant case: the condition depends
                            // on a parameter that's constant per-trace but varies across traces.
                            //
                            // Strategy: The ITE condition partitions traces into two classes.
                            // Learn that this condition (or its negation) is preserved by
                            // transitions. For a constant parameter P in condition (x <= P),
                            // if P never changes then the truth of (x <= P) may be preserved
                            // when x follows a specific pattern.
                            //
                            // For three_dots_moving_2: condition is (B <= F) where F is constant.
                            // If initially B > F, then D = B - 1, so D could still be > F or <= F.
                            // If initially B <= F, then D = B + 1, so eventually B catches up to F.
                            //
                            // Key insight: We should track the constant parameter as a variable
                            // that constrains the reachable state space. Since we can't learn
                            // a fixed truth value, we try to simplify the problem by:
                            // 1. Checking if one branch leads to termination (safety proven)
                            // 2. Checking if the constant creates a bound on other variables
                            //
                            // For now, try to learn that the constant argument provides an
                            // implicit bound: if C is constant and appears in (X <= C), then
                            // we might have X <= C + k for some small k as an invariant.

                            // Check if the ITE condition involves a comparison with a constant arg
                            if let ChcExpr::Op(op, cond_args) = &candidate.canonical_cond {
                                let is_comparison =
                                    matches!(op, ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt);
                                if is_comparison && cond_args.len() == 2 {
                                    // Try to learn a relaxed bound based on the comparison
                                    // e.g., if condition is (a <= c) where c is constant,
                                    // try learning a <= c + 1, a <= c + 2, etc. as invariants
                                    let lhs = &cond_args[0];
                                    let rhs = &cond_args[1];

                                    let constant_positions =
                                        self.detect_constant_arguments(candidate.body_pred);

                                    // Check if one side is purely a constant argument
                                    let lhs_is_const = Self::expr_is_pure_constant_arg(
                                        lhs,
                                        &candidate.canonical_vars,
                                        &constant_positions,
                                    );
                                    let rhs_is_const = Self::expr_is_pure_constant_arg(
                                        rhs,
                                        &candidate.canonical_vars,
                                        &constant_positions,
                                    );

                                    let const_side = if lhs_is_const {
                                        Some((lhs.as_ref().clone(), rhs.as_ref().clone(), false))
                                    } else if rhs_is_const {
                                        Some((rhs.as_ref().clone(), lhs.as_ref().clone(), true))
                                    } else {
                                        None
                                    };

                                    if let Some((const_expr, var_expr, is_rhs_const)) = const_side {
                                        // Try relaxed bounds: var_expr <= const_expr + k
                                        for k in [0i128, 1, 2, 3] {
                                            let relaxed_bound = if k == 0 {
                                                const_expr.clone()
                                            } else {
                                                ChcExpr::add(const_expr.clone(), ChcExpr::Int(k))
                                            };

                                            let relaxed_invariant = match (op, is_rhs_const) {
                                                (ChcOp::Le, false) | (ChcOp::Ge, true) => {
                                                    // (var <= const) or (const >= var) => var <= const + k
                                                    ChcExpr::le(var_expr.clone(), relaxed_bound)
                                                }
                                                (ChcOp::Lt, false) | (ChcOp::Gt, true) => {
                                                    // (var < const) or (const > var) => var < const + k
                                                    ChcExpr::lt(var_expr.clone(), relaxed_bound)
                                                }
                                                (ChcOp::Ge, false) | (ChcOp::Le, true) => {
                                                    // (var >= const) or (const <= var) => var >= const - k
                                                    let lower_bound = if k == 0 {
                                                        const_expr.clone()
                                                    } else {
                                                        ChcExpr::sub(
                                                            const_expr.clone(),
                                                            ChcExpr::Int(k),
                                                        )
                                                    };
                                                    ChcExpr::ge(var_expr.clone(), lower_bound)
                                                }
                                                (ChcOp::Gt, false) | (ChcOp::Lt, true) => {
                                                    // (var > const) or (const < var) => var > const - k
                                                    let lower_bound = if k == 0 {
                                                        const_expr.clone()
                                                    } else {
                                                        ChcExpr::sub(
                                                            const_expr.clone(),
                                                            ChcExpr::Int(k),
                                                        )
                                                    };
                                                    ChcExpr::gt(var_expr.clone(), lower_bound)
                                                }
                                                _ => continue,
                                            };

                                            // Check if this relaxed bound holds at init
                                            let init_check = ChcExpr::and(
                                                candidate.fact_constraint.clone(),
                                                ChcExpr::not(relaxed_invariant.clone()),
                                            );
                                            // #7984: Use persistent executor backend for integer arithmetic.
                                            let init_result =
                                                self.check_sat_via_executor_backend(&init_check);
                                            if !matches!(
                                                init_result,
                                                SmtResult::Unsat
                                                    | SmtResult::UnsatWithCore(_)
                                                    | SmtResult::UnsatWithFarkas(_)
                                            ) {
                                                continue; // Doesn't hold at init
                                            }

                                            // Check if it's inductive and not already learned
                                            let blocking = ChcExpr::not(relaxed_invariant.clone());
                                            let already_learned = self.frames.iter().any(|f| {
                                                f.contains_lemma(
                                                    candidate.body_pred,
                                                    &relaxed_invariant,
                                                )
                                            });
                                            if self.is_inductive_blocking(
                                                &blocking,
                                                candidate.body_pred,
                                                0,
                                            ) && !already_learned
                                            {
                                                if self.config.verbose {
                                                    safe_eprintln!(
                                                        "PDR: Learned relaxed ITE bound for pred {}: {} (k={})",
                                                        candidate.body_pred.index(),
                                                        relaxed_invariant,
                                                        k
                                                    );
                                                }
                                                self.add_lemma_to_frame(
                                                    Lemma::new(
                                                        candidate.body_pred,
                                                        relaxed_invariant,
                                                        0,
                                                    ),
                                                    0,
                                                );
                                                learned = true;
                                                break; // Found an invariant, stop trying larger k
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                SmtResult::Unknown => {}
            }
        }

        // Process grounded invariants from model-based case analysis
        for gi in grounded_invariants {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Checking grounded invariant for pred {}: {}",
                    gi.pred.index(),
                    gi.formula
                );
            }

            // Check if this invariant holds at init and is inductive
            let blocking = ChcExpr::not(gi.formula.clone());
            if self.is_inductive_blocking(&blocking, gi.pred, 0) {
                if !self
                    .frames
                    .iter()
                    .any(|f| f.contains_lemma(gi.pred, &gi.formula))
                {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Learned grounded ITE invariant for pred {}: {}",
                            gi.pred.index(),
                            gi.formula
                        );
                    }
                    self.add_lemma_to_frame(Lemma::new(gi.pred, gi.formula, 0), 0);
                    learned = true;
                }
            } else if self.config.verbose {
                safe_eprintln!("PDR: Grounded invariant not inductive: {}", gi.formula);
            }
        }

        learned
    }
}
