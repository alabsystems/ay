// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Clause-level inlining operations.
//!
//! Contains the low-level functions that perform actual clause inlining:
//! applying definitions, substituting variables, and handling fresh variable
//! generation for capture avoidance.

use crate::{ChcExpr, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::{fresh_var_name, ClauseInliner, CompositionStep};

/// Everything one definition-inlining produced.
///
/// `body_preds` and `constraint` are the inlining OUTPUT. The other two fields
/// are purely observational records for ground back-translation
/// (#item4-ground-witness-backtranslation): they let the back-translator
/// rebuild, by evaluation, values that inlining projected out of the surviving
/// clause. Nothing in the transformation reads them.
pub(super) struct InlineResult {
    /// Body predicates of the definition, in the caller's variable space.
    pub(super) body_preds: Vec<(PredicateId, Vec<ChcExpr>)>,
    /// Constraint contributed by the definition, in the caller's space.
    pub(super) constraint: Option<ChcExpr>,
    /// `(fresh_linking_var, caller_space_defining_expression)` for the fresh
    /// variables introduced at HEAD-ARGUMENT positions.
    pub(super) linking_defs: Vec<(ChcVar, ChcExpr)>,
    /// The COMPLETE rename this inlining applied to the defining clause:
    /// `(def_clause_var_name, composite_space_expression)`.
    ///
    /// Distinct from `linking_defs`, which covers only fresh head-argument
    /// linking variables. This covers EVERY variable of the definition,
    /// including its BODY-LOCALS. Those are existential in the ORIGINAL clause
    /// — no equality names them, no premise pins them — but in the COMPOSITE
    /// they are ordinary named variables that the level-BMC model assigns, so
    /// recording the rename is what lets ground back-translation read the
    /// witness back instead of sort-defaulting a value it cannot derive.
    pub(super) var_renames: Vec<(String, ChcExpr)>,
}

impl ClauseInliner {
    /// Apply definitions to inline predicates in a clause while recording a
    /// [`CompositionStep`] for every predicate, so the invalidity
    /// back-translator can reconstruct the collapsed derivation chain
    /// (#chc25-deriv-expansion).
    ///
    /// Recording is a pure side-observation and never affects inlining output.
    /// Each step captures the predicate's CALL ARGUMENTS as they appear in the
    /// (progressively freshened) composite variable space; reading their model
    /// values from the composite derivation entry yields that predicate's
    /// argument values at the derivation step.
    pub(super) fn apply_defs_tracked(
        &self,
        clause: &HornClause,
        defs: &FxHashMap<PredicateId, HornClause>,
        def_input_indices: &FxHashMap<PredicateId, usize>,
    ) -> (HornClause, Vec<CompositionStep>) {
        let mut pending_preds = clause.body.predicates.clone();
        let mut final_preds: Vec<(PredicateId, Vec<ChcExpr>)> = Vec::new();
        let mut constraints: Vec<ChcExpr> = clause.body.constraint.iter().cloned().collect();
        let mut steps: Vec<CompositionStep> = Vec::new();

        while let Some((pred_id, args)) = pending_preds.pop() {
            if let Some(def_clause) = defs.get(&pred_id) {
                let inlined = self.inline_clause(def_clause, &args);
                steps.push(CompositionStep {
                    inlined_pred: pred_id,
                    call_args: args.clone(),
                    def_clause: def_clause.clone(),
                    def_input_index: def_input_indices.get(&pred_id).copied(),
                    linking_defs: inlined.linking_defs,
                    var_renames: inlined.var_renames,
                });
                pending_preds.extend(inlined.body_preds);
                if let Some(c) = inlined.constraint {
                    constraints.push(c);
                }
            } else {
                final_preds.push((pred_id, args));
            }
        }

        let final_constraint = constraints.into_iter().reduce(ChcExpr::and);

        (
            HornClause::new(
                ClauseBody::new(final_preds, final_constraint),
                clause.head.clone(),
            ),
            steps,
        )
    }

    /// Inline a clause definition with the given arguments.
    ///
    /// Given defining clause `H(x, y) ⇐ B₁(x), B₂(y), φ(x, y)` and call `H(a, b)`:
    /// 1. Create fresh variables x', y' to avoid capture
    /// 2. Add constraint `x' = a ∧ y' = b`
    /// 3. Return body `B₁(x'), B₂(y')` and constraint `φ(x', y') ∧ x' = a ∧ y' = b`
    ///
    /// [`InlineResult::linking_defs`] records, for each fresh variable this call
    /// introduced at a head-argument position, the caller-space expression it
    /// stands for (`x' ↦ a`); [`InlineResult::var_renames`] records the FULL
    /// def-var → composite-space rename, body-locals included. Ground
    /// back-translation replays both by EVALUATION to rebuild the values that
    /// inlining existentially projects away, instead of solving for them
    /// (#item4-ground-witness-backtranslation). Purely observational: the
    /// inlined clause is byte-for-byte what it was before.
    pub(super) fn inline_clause(
        &self,
        def_clause: &HornClause,
        call_args: &[ChcExpr],
    ) -> InlineResult {
        // Get head arguments (formal parameters)
        let head_args: &[ChcExpr] = match &def_clause.head {
            ClauseHead::Predicate(_, args) => args,
            ClauseHead::False => {
                return InlineResult {
                    body_preds: Vec::new(),
                    constraint: None,
                    linking_defs: Vec::new(),
                    var_renames: Vec::new(),
                }
            }
        };

        // Optimization: when all head args are plain Vars and there are no
        // body-local variables, substitute directly (head_var → call_arg)
        // without introducing fresh variables. This avoids polluting PDR's
        // model with auxiliary variables that don't exist in the original problem.
        let all_head_vars = head_args.iter().all(|a| matches!(a, ChcExpr::Var(_)));
        let head_var_names: FxHashSet<&str> = head_args
            .iter()
            .filter_map(|a| match a {
                ChcExpr::Var(v) => Some(v.name.as_str()),
                _ => None,
            })
            .collect();
        // SOUNDNESS: the direct path also requires PAIRWISE-DISTINCT head var
        // names. A repeated head variable (e.g. `P(v, v)`) would build the
        // substitution [(v, a), (v, b)]; map collapse (last-wins) then yields
        // φ(b) and silently DROPS the implied positional equality a = b —
        // weakening the body, deriving more, a wrong-Unsafe class. The
        // fresh-vars path links repeated positions through one canonical
        // fresh variable (#7897) and handles this correctly.
        let distinct_head_vars = all_head_vars && head_var_names.len() == head_args.len();
        let has_body_local_vars = if distinct_head_vars {
            let body_vars = def_clause.body.vars();
            body_vars
                .iter()
                .any(|v| !head_var_names.contains(v.name.as_str()))
        } else {
            true // Complex/repeated head args always need fresh variables
        };

        if distinct_head_vars && !has_body_local_vars {
            return self.inline_clause_direct(def_clause, head_args, call_args);
        }

        // Fallback: fresh variable approach for complex cases
        self.inline_clause_with_fresh_vars(def_clause, head_args, call_args)
    }

    /// Direct substitution: map each head Var directly to the corresponding call arg.
    /// Safe when there are no body-local variables to capture.
    fn inline_clause_direct(
        &self,
        def_clause: &HornClause,
        head_args: &[ChcExpr],
        call_args: &[ChcExpr],
    ) -> InlineResult {
        let subst: Vec<(ChcVar, ChcExpr)> = head_args
            .iter()
            .zip(call_args.iter())
            .filter_map(|(head_arg, call_arg)| {
                if let ChcExpr::Var(v) = head_arg {
                    Some((v.clone(), call_arg.clone()))
                } else {
                    None // Shouldn't happen (caller checks all_head_vars)
                }
            })
            .collect();

        let new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = def_clause
            .body
            .predicates
            .iter()
            .map(|(pred_id, args)| {
                let new_args: Vec<ChcExpr> =
                    args.iter().map(|arg| arg.substitute(&subst)).collect();
                (*pred_id, new_args)
            })
            .collect();

        let subst_constraint = def_clause
            .body
            .constraint
            .as_ref()
            .map(|c| c.substitute(&subst));

        // The direct path introduces no fresh variables, so there are no
        // LINKING definitions for ground back-translation to replay. The rename
        // is still worth recording: it maps each head variable to the
        // caller-space call-argument EXPRESSION, which evaluates in the
        // composite environment just as well as a fresh name does. This path
        // has no body-locals by construction (that is its precondition), so it
        // adds nothing the call-argument seeding would not already find — but
        // keeping the two paths uniform means the consumer never has to ask
        // which one ran.
        InlineResult {
            body_preds: new_body_preds,
            constraint: subst_constraint,
            linking_defs: Vec::new(),
            var_renames: subst
                .into_iter()
                .map(|(var, expr)| (var.name, expr))
                .collect(),
        }
    }

    /// Fresh variable approach: create fresh variables and add equality constraints.
    /// Required when body-local variables exist or head args are complex expressions.
    fn inline_clause_with_fresh_vars(
        &self,
        def_clause: &HornClause,
        head_args: &[ChcExpr],
        call_args: &[ChcExpr],
    ) -> InlineResult {
        // Create fresh variables for each head argument position
        let fresh_vars: Vec<ChcVar> = head_args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let sort = arg.sort();
                let prefix = if let ChcExpr::Var(v) = arg {
                    v.name.clone()
                } else {
                    format!("arg{i}")
                };
                ChcVar::new(fresh_var_name(&prefix), sort)
            })
            .collect();

        // Build substitution in two passes to handle shared variables correctly.
        // A variable like `A` can appear both as a plain Var head arg AND inside
        // an expression head arg (e.g., `f(1+A, A)`). Processing Var args first
        // establishes canonical fresh names, then expression args reuse them (#5523).
        let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        let mut expr_equalities: Vec<ChcExpr> = Vec::new();

        // Pass 1: Var head args → canonical substitutions.
        for (i, arg) in head_args.iter().enumerate() {
            if let ChcExpr::Var(v) = arg {
                if !subst.iter().any(|(sv, _)| sv.name == v.name) {
                    subst.push((v.clone(), ChcExpr::var(fresh_vars[i].clone())));
                }
            }
        }

        // Pass 2: Expression head args → freshen remaining constituent vars
        // and build equality constraints. Variables already in subst (from Var
        // head args) are reused, keeping a single canonical fresh name.
        for (i, arg) in head_args.iter().enumerate() {
            if !matches!(arg, ChcExpr::Var(_)) {
                // #2660: Expression head arg — freshen constituent vars to
                // avoid capture, then add equality fresh_pos = expr[freshened].
                for v in arg.vars() {
                    if !subst.iter().any(|(sv, _)| sv.name == v.name) {
                        let fresh = ChcVar::new(fresh_var_name(&v.name), v.sort.clone());
                        subst.push((v, ChcExpr::var(fresh)));
                    }
                }
                // Apply freshening to the expression using all substitutions
                let freshened_expr = arg.substitute(&subst);
                expr_equalities.push(ChcExpr::eq(
                    ChcExpr::var(fresh_vars[i].clone()),
                    freshened_expr,
                ));
            }
        }

        // Freshen body-local variables to avoid capture with the calling clause's
        // variables (#5523). A body-local variable is any variable in the body
        // (predicates or constraint) that was not already freshened above (i.e.,
        // not a head variable or expression-head constituent).
        let already_freshened: FxHashSet<String> =
            subst.iter().map(|(v, _)| v.name.clone()).collect();
        for v in def_clause.body.vars() {
            if !already_freshened.contains(&v.name) {
                let fresh = ChcVar::new(fresh_var_name(&v.name), v.sort.clone());
                subst.push((v, ChcExpr::var(fresh)));
            }
        }

        // Apply substitution to body predicates
        let new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = def_clause
            .body
            .predicates
            .iter()
            .map(|(pred_id, args)| {
                let new_args: Vec<ChcExpr> =
                    args.iter().map(|arg| arg.substitute(&subst)).collect();
                (*pred_id, new_args)
            })
            .collect();

        // Apply substitution to constraint
        let subst_constraint = def_clause
            .body
            .constraint
            .as_ref()
            .map(|c| c.substitute(&subst));

        // Build equalities: canonical_fresh = call_arg.
        // SOUNDNESS FIX (#7897): When a Var appears at multiple head positions
        // (e.g., `Post(1, v, v)`), each position gets its own fresh_vars[i],
        // but the substitution maps `v` to only ONE canonical fresh variable
        // (from Pass 1). We must use the canonical variable for the equality,
        // not the position-specific one, so that call_args at shared positions
        // are correctly linked through the same fresh variable.
        //
        // These same pairs are handed back as the LINKING DEFINITIONS: each
        // canonical fresh variable is DEFINED by the caller-space call argument
        // it was equated to, so ground back-translation can rebuild its value by
        // evaluation. Only the first binding of a repeated head variable is
        // recorded — the later positions are equalities the composite already
        // carries, not independent definitions, and recording them would let a
        // second (equal-by-constraint) expression overwrite the first.
        let mut linking_defs: Vec<(ChcVar, ChcExpr)> = Vec::new();
        let arg_equalities: Vec<ChcExpr> = head_args
            .iter()
            .enumerate()
            .zip(call_args.iter())
            .map(|((i, head_arg), actual)| {
                let canonical_fresh = if let ChcExpr::Var(v) = head_arg {
                    // Look up the canonical fresh variable from subst
                    subst
                        .iter()
                        .find(|(sv, _)| sv.name == v.name)
                        .map(|(_, expr)| expr.clone())
                        .unwrap_or_else(|| ChcExpr::var(fresh_vars[i].clone()))
                } else {
                    ChcExpr::var(fresh_vars[i].clone())
                };
                if let ChcExpr::Var(fresh) = &canonical_fresh {
                    if !linking_defs.iter().any(|(v, _)| v.name == fresh.name) {
                        linking_defs.push((fresh.clone(), actual.clone()));
                    }
                }
                ChcExpr::eq(canonical_fresh, actual.clone())
            })
            .collect();

        // Combine all constraints: arg equalities + expression head equalities + original
        let all_constraints: Vec<ChcExpr> = arg_equalities
            .into_iter()
            .chain(expr_equalities)
            .chain(subst_constraint)
            .collect();

        let final_constraint = if all_constraints.is_empty() {
            None
        } else {
            Some(
                all_constraints
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .expect("all_constraints is non-empty after is_empty check"),
            )
        };

        InlineResult {
            body_preds: new_body_preds,
            constraint: final_constraint,
            linking_defs,
            // `subst` is complete by construction: pass 1 covered the head
            // variables, pass 2 the expression-head constituents, and the loop
            // above every remaining body variable. Handing it over is what lets
            // ground back-translation name a body-local's composite counterpart
            // EXACTLY. It must not be re-derived by prefix-matching the
            // `{orig}__inline_{counter}` scheme downstream: the same original
            // variable is freshened once per call site, so a prefix scan is
            // ambiguous (measured: up to 396 candidates for one name on the
            // iterator_count archetype).
            var_renames: subst
                .into_iter()
                .map(|(var, expr)| (var.name, expr))
                .collect(),
        }
    }

    /// Compute the size of an expression (number of nodes).
    pub(super) fn expr_size(expr: &ChcExpr) -> usize {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_) => 1,
            ChcExpr::Op(_, args) => 1 + args.iter().map(|a| Self::expr_size(a)).sum::<usize>(),
            ChcExpr::PredicateApp(_, _, args) => {
                1 + args.iter().map(|a| Self::expr_size(a)).sum::<usize>()
            }
            ChcExpr::ConstArrayMarker(_) => 1,
            ChcExpr::IsTesterMarker(_) => 1,
            ChcExpr::FuncApp(_, _, args) => {
                1 + args.iter().map(|a| Self::expr_size(a)).sum::<usize>()
            }
            ChcExpr::ConstArray(_ks, val) => 1 + Self::expr_size(val),
        })
    }

    /// Normalize a defining clause so all head arguments are plain variables.
    ///
    /// For `P(x+1, y) <= C(x, y)`, rewrites to
    /// `P(f0, f1) <= (f0 = x'+1) ∧ (f1 = y') ∧ C(x', y')`
    /// so `synthesize_interpretation` can extract formal parameters. (#5295)
    pub(super) fn normalize_head_for_back_translation(clause: &HornClause) -> HornClause {
        let head_args = match &clause.head {
            ClauseHead::Predicate(_, args) => args,
            ClauseHead::False => return clause.clone(),
        };

        let needs_normalization = head_args.iter().any(|a| !matches!(a, ChcExpr::Var(_)));
        if !needs_normalization {
            return clause.clone();
        }

        let pred_id = clause.head.predicate_id().expect("checked above");
        let (fresh_vars, equalities, subst) = Self::build_head_normalization(head_args);

        let new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = clause
            .body
            .predicates
            .iter()
            .map(|(pid, args)| {
                let new_args = args.iter().map(|a| a.substitute(&subst)).collect();
                (*pid, new_args)
            })
            .collect();

        let subst_constraint = clause
            .body
            .constraint
            .as_ref()
            .map(|c| c.substitute(&subst));
        let mut all_constraints: Vec<ChcExpr> = equalities;
        if let Some(c) = subst_constraint {
            all_constraints.push(c);
        }

        let final_constraint = all_constraints.into_iter().reduce(ChcExpr::and);

        let new_head = ClauseHead::Predicate(
            pred_id,
            fresh_vars.iter().map(|v| ChcExpr::var(v.clone())).collect(),
        );

        HornClause::new(ClauseBody::new(new_body_preds, final_constraint), new_head)
    }

    /// Build fresh variables and substitution for normalizing complex head args.
    ///
    /// Returns `(fresh_vars, equalities, substitution)` where:
    /// - `fresh_vars[i]` is a fresh variable replacing `head_args[i]`
    /// - `equalities` are `fresh_i = expr_i` for non-Var head args
    /// - `substitution` maps original vars to fresh vars
    fn build_head_normalization(
        head_args: &[ChcExpr],
    ) -> (Vec<ChcVar>, Vec<ChcExpr>, Vec<(ChcVar, ChcExpr)>) {
        let fresh_vars: Vec<ChcVar> = head_args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let sort = arg.sort();
                let prefix = if let ChcExpr::Var(v) = arg {
                    v.name.clone()
                } else {
                    format!("bt_arg{i}")
                };
                ChcVar::new(fresh_var_name(&prefix), sort)
            })
            .collect();

        let mut equalities: Vec<ChcExpr> = Vec::new();
        let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (i, arg) in head_args.iter().enumerate() {
            match arg {
                ChcExpr::Var(v) => {
                    subst.push((v.clone(), ChcExpr::var(fresh_vars[i].clone())));
                }
                expr => {
                    for v in expr.vars() {
                        if !subst.iter().any(|(sv, _)| sv.name == v.name) {
                            let fresh = ChcVar::new(fresh_var_name(&v.name), v.sort.clone());
                            subst.push((v, ChcExpr::var(fresh)));
                        }
                    }
                    let freshened_expr = expr.substitute(&subst);
                    equalities.push(ChcExpr::eq(
                        ChcExpr::var(fresh_vars[i].clone()),
                        freshened_expr,
                    ));
                }
            }
        }
        (fresh_vars, equalities, subst)
    }
}
