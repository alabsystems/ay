// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality replay for `PropagateValues` proof reconstruction.

use super::*;

enum FoldShape {
    Same(Vec<TermId>),
    Swapped,
    Collapsing,
}

impl PropagationChainPlanner<'_> {
    /// Replay the pass's `rewrite` on `t` under the licensing environment of
    /// entries with stamp `<= stamp`, emitting an equality derivation for
    /// every change. Outer `None` fails the plan (unsupported shape or
    /// budget); `Some(Unchanged)` means the pass leaves `t` as-is.
    pub(super) fn plan_derive_eq(
        &mut self,
        cx: &mut PlanCx<'_>,
        t: TermId,
        stamp: u32,
    ) -> Option<EqRes> {
        if let Some(&memoized) = cx.eq_memo.get(&(t, stamp)) {
            return memoized;
        }
        cx.spend(1)?;
        let result = self.plan_derive_eq_inner(cx, t, stamp);
        cx.eq_memo.insert((t, stamp), result);
        result
    }

    fn plan_derive_eq_inner(
        &mut self,
        cx: &mut PlanCx<'_>,
        t: TermId,
        stamp: u32,
    ) -> Option<EqRes> {
        // Direct substitution first (mirrors `rewrite`).
        if let Some(&(value, source, entry_stamp)) = cx.entry_by_expr.get(&t) {
            if entry_stamp <= stamp {
                let id = self.plan_derive_clause(cx, source)?;
                return Some(EqRes::Changed {
                    to: value,
                    eq_term: source,
                    id,
                });
            }
        }
        match self.terms.get(t).clone() {
            TermData::Const(_) | TermData::Var(_, _) => Some(EqRes::Unchanged),
            // The pass passes binders through unchanged.
            TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                Some(EqRes::Unchanged)
            }
            // Slice 1 replays Not/Ite only when their children are untouched.
            TermData::Not(inner) => match self.plan_derive_eq(cx, inner, stamp)? {
                EqRes::Unchanged => Some(EqRes::Unchanged),
                EqRes::Changed { .. } => None,
            },
            TermData::Ite(condition, then_branch, else_branch) => {
                let unchanged = [condition, then_branch, else_branch].into_iter().try_fold(
                    true,
                    |acc, child| match self.plan_derive_eq(cx, child, stamp)? {
                        EqRes::Unchanged => Some(acc),
                        EqRes::Changed { .. } => Some(false),
                    },
                )?;
                unchanged.then_some(EqRes::Unchanged)
            }
            TermData::App(symbol, args) => self.plan_derive_app_eq(cx, t, stamp, symbol, args),
            // Future TermData variants: fail the plan (fail-closed).
            _ => None,
        }
    }

    fn plan_derive_app_eq(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        stamp: u32,
        symbol: Symbol,
        args: Vec<TermId>,
    ) -> Option<EqRes> {
        let mut child_results = Vec::with_capacity(args.len());
        let mut any_changed = false;
        for &arg in &args {
            let result = self.plan_derive_eq(cx, arg, stamp)?;
            any_changed |= matches!(result, EqRes::Changed { .. });
            child_results.push(result);
        }
        if !any_changed {
            return Some(EqRes::Unchanged);
        }
        let new_args = args
            .iter()
            .zip(&child_results)
            .map(|(&arg, result)| match result {
                EqRes::Unchanged => arg,
                EqRes::Changed { to, .. } => *to,
            })
            .collect::<Vec<_>>();
        let folded =
            PropagateValues::fold_rebuild(self.terms, symbol.clone(), term, new_args.clone());
        // Mirror `rewrite`'s post-fold map lookup.
        let tail = cx
            .entry_by_expr
            .get(&folded)
            .copied()
            .filter(|&(_, _, entry_stamp)| entry_stamp <= stamp);
        if tail.map_or(folded, |(value, _, _)| value) == term {
            return Some(EqRes::Unchanged);
        }
        let (eq_term, id) =
            self.plan_fold_bridge(cx, term, folded, &symbol, &args, &new_args, &child_results)?;
        let Some((value, source, _)) = tail else {
            return Some(EqRes::Changed {
                to: folded,
                eq_term,
                id,
            });
        };
        let source_id = self.plan_derive_clause(cx, source)?;
        let final_eq = self
            .terms
            .mk_app(Symbol::named("="), [term, value], Sort::Bool);
        let final_id = cx.chain.add_rule_step(
            AletheRule::Trans,
            vec![final_eq],
            vec![id, source_id],
            Vec::new(),
        );
        Some(EqRes::Changed {
            to: value,
            eq_term: final_eq,
            id: final_id,
        })
    }

    fn plan_fold_bridge(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        symbol: &Symbol,
        args: &[TermId],
        new_args: &[TermId],
        child_results: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        match self.classify_fold_shape(folded, symbol, args.len(), new_args) {
            FoldShape::Same(folded_args) => {
                self.plan_same_shape_fold(cx, term, folded, args, &folded_args, child_results)
            }
            FoldShape::Swapped => self.plan_swapped_equality_fold(
                cx,
                term,
                folded,
                symbol,
                args,
                new_args,
                child_results,
            ),
            FoldShape::Collapsing => self
                .plan_collapsing_fold(cx, term, folded, symbol, args, new_args, child_results)
                .or_else(|| {
                    self.plan_bool_eq_const_fold(
                        cx,
                        term,
                        folded,
                        symbol,
                        args,
                        new_args,
                        child_results,
                    )
                }),
        }
    }

    fn classify_fold_shape(
        &self,
        folded: TermId,
        symbol: &Symbol,
        arity: usize,
        new_args: &[TermId],
    ) -> FoldShape {
        let TermData::App(folded_symbol, folded_args) = self.terms.get(folded) else {
            return FoldShape::Collapsing;
        };
        if folded_symbol != symbol || folded_args.len() != arity {
            return FoldShape::Collapsing;
        }
        if folded_args
            .iter()
            .zip(new_args)
            .all(|(left, right)| left == right)
        {
            return FoldShape::Same(folded_args.clone());
        }
        if symbol.name() == "="
            && new_args.len() == 2
            && folded_args[0] == new_args[1]
            && folded_args[1] == new_args[0]
        {
            return FoldShape::Swapped;
        }
        FoldShape::Collapsing
    }

    fn congruence_premises(
        args: &[TermId],
        child_results: &[EqRes],
        target_args: &[TermId],
    ) -> Option<Vec<ProofId>> {
        let mut premises = Vec::new();
        for ((&old_arg, result), &target_arg) in args.iter().zip(child_results).zip(target_args) {
            if old_arg == target_arg {
                continue;
            }
            match result {
                EqRes::Changed { to, id, .. } if *to == target_arg => premises.push(*id),
                _ => return None,
            }
        }
        Some(premises)
    }

    fn plan_same_shape_fold(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        args: &[TermId],
        folded_args: &[TermId],
        child_results: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        let premises = Self::congruence_premises(args, child_results, folded_args)?;
        let equality = self
            .terms
            .mk_app(Symbol::named("="), [term, folded], Sort::Bool);
        let id = cx
            .chain
            .add_rule_step(AletheRule::Cong, vec![equality], premises, Vec::new());
        Some((equality, id))
    }

    fn plan_swapped_equality_fold(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        symbol: &Symbol,
        args: &[TermId],
        new_args: &[TermId],
        child_results: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        // Congruence reaches the raw rebuilt spelling; symmetry and
        // transitivity bridge its canonical equality argument order.
        let premises = Self::congruence_premises(args, child_results, new_args)?;
        let rebuilt = self
            .terms
            .mk_app(symbol.clone(), new_args.to_vec(), Sort::Bool);
        if rebuilt == term || rebuilt == folded {
            return None;
        }
        let term_to_rebuilt = self
            .terms
            .mk_app(Symbol::named("="), [term, rebuilt], Sort::Bool);
        let congruence = cx.chain.add_rule_step(
            AletheRule::Cong,
            vec![term_to_rebuilt],
            premises,
            Vec::new(),
        );
        let rebuilt_to_folded =
            self.terms
                .mk_app(Symbol::named("="), [rebuilt, folded], Sort::Bool);
        let symmetry = cx.chain.add_rule_step(
            AletheRule::EqSymmetric,
            vec![rebuilt_to_folded],
            Vec::new(),
            Vec::new(),
        );
        let term_to_folded = self
            .terms
            .mk_app(Symbol::named("="), [term, folded], Sort::Bool);
        let transitivity = cx.chain.add_rule_step(
            AletheRule::Trans,
            vec![term_to_folded],
            vec![congruence, symmetry],
            Vec::new(),
        );
        Some((term_to_folded, transitivity))
    }

    fn plan_collapsing_fold(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        symbol: &Symbol,
        args: &[TermId],
        new_args: &[TermId],
        child_results: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        let sort = self.terms.sort(term).clone();
        let rebuilt = self.terms.mk_app(symbol.clone(), new_args.to_vec(), sort);
        if rebuilt == term
            || rebuilt == folded
            || !new_args
                .iter()
                .all(|&arg| matches!(self.terms.get(arg), TermData::Const(_)))
        {
            return None;
        }
        let premises = Self::congruence_premises(args, child_results, new_args)?;
        let term_to_rebuilt = self
            .terms
            .mk_app(Symbol::named("="), [term, rebuilt], Sort::Bool);
        let congruence = cx.chain.add_rule_step(
            AletheRule::Cong,
            vec![term_to_rebuilt],
            premises,
            Vec::new(),
        );
        let rebuilt_to_folded =
            self.terms
                .mk_app(Symbol::named("="), [rebuilt, folded], Sort::Bool);
        let evaluation = self.plan_closed_fold_evaluation(cx, rebuilt, new_args, rebuilt_to_folded);
        let term_to_folded = self
            .terms
            .mk_app(Symbol::named("="), [term, folded], Sort::Bool);
        let transitivity = cx.chain.add_rule_step(
            AletheRule::Trans,
            vec![term_to_folded],
            vec![congruence, evaluation],
            Vec::new(),
        );
        Some((term_to_folded, transitivity))
    }

    /// Bool `(= x true/false)` fold bridge (#ppp-l3, `mk_eq` Boolean
    /// simplifications): a substitution turns exactly one side of a Boolean
    /// equality into the constant `true`/`false` and the canonical rebuild
    /// folds the equality to `x` / `(not x)`. Derives
    /// `(cl (= term folded))` with EXISTING rules only — `cong` to the raw
    /// rebuilt spelling `R`, then an `equiv_pos`/`equiv_neg` chain with the
    /// `true`/`(not false)` tautology closing `(cl (= R folded))`, and
    /// `trans`. Works for arbitrary theory atoms `x` (no bounded-evaluation
    /// requirement); every step is re-derived by the untouched strict
    /// checker.
    fn plan_bool_eq_const_fold(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        symbol: &Symbol,
        args: &[TermId],
        new_args: &[TermId],
        child_results: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        if symbol.name() != "=" || new_args.len() != 2 {
            return None;
        }
        let true_term = self.terms.true_term();
        let false_term = self.terms.false_term();
        // Exactly one constant side; the other a Bool-sorted non-constant.
        let (x, constant) = match (
            matches!(self.terms.get(new_args[0]), TermData::Const(_)),
            matches!(self.terms.get(new_args[1]), TermData::Const(_)),
        ) {
            (false, true) => (new_args[0], new_args[1]),
            (true, false) => (new_args[1], new_args[0]),
            _ => return None,
        };
        if constant != true_term && constant != false_term {
            return None;
        }
        if self.terms.sort(x) != &Sort::Bool {
            return None;
        }
        // Mirror the exact `mk_eq` fold this bridge certifies.
        let expected = if constant == true_term {
            x
        } else {
            self.terms.mk_not(x)
        };
        if folded != expected {
            return None;
        }
        cx.spend(12)?;
        let rebuilt = self
            .terms
            .mk_app(symbol.clone(), new_args.to_vec(), Sort::Bool);
        if rebuilt == term || rebuilt == folded {
            return None;
        }
        let premises = Self::congruence_premises(args, child_results, new_args)?;
        let term_to_rebuilt = self
            .terms
            .mk_app(Symbol::named("="), [term, rebuilt], Sort::Bool);
        let congruence = cx.chain.add_rule_step(
            AletheRule::Cong,
            vec![term_to_rebuilt],
            premises,
            Vec::new(),
        );
        let bridge = self.plan_bool_eq_const_bridge(cx, rebuilt, x, constant, folded)?;
        let term_to_folded = self
            .terms
            .mk_app(Symbol::named("="), [term, folded], Sort::Bool);
        let transitivity = cx.chain.add_rule_step(
            AletheRule::Trans,
            vec![term_to_folded],
            vec![congruence, bridge],
            Vec::new(),
        );
        Some((term_to_folded, transitivity))
    }

    /// `(cl (= R folded))` where `R` is the raw spelling `(= x true|false)`
    /// (either stored argument order) and `folded` is the canonical fold
    /// (`x`, resp. `(not x)`).
    ///
    /// With `E := (= R folded)` and `K` the constant-discharge tautology
    /// (`true` rule for `true`, `(cl (not false))` for `false`):
    ///
    /// ```text
    /// A  := equiv_pos(R)  ⊕ K   -- (cl (not R) folded)
    /// B  := equiv_neg(R)  ⊕ K   -- (cl R (not folded))
    /// r1 := equiv_neg2(E) ⊕ A   -- (cl E folded)
    /// r2 := equiv_neg1(E) ⊕ B   -- (cl E (not folded))
    /// E  := r1 ⊕ r2             -- (cl E)
    /// ```
    ///
    /// All resolutions use the checker's decoded set semantics, so the
    /// canonical/raw `not` spellings and a double-negation collapse in
    /// `folded` (when `x` is itself a negation) resolve exactly.
    fn plan_bool_eq_const_bridge(
        &mut self,
        cx: &mut PlanCx<'_>,
        rebuilt: TermId,
        x: TermId,
        constant: TermId,
        folded: TermId,
    ) -> Option<ProofId> {
        let TermData::App(_, rebuilt_args) = self.terms.get(rebuilt) else {
            return None;
        };
        let x_first = rebuilt_args[0] == x;
        let true_term = self.terms.true_term();
        let positive = constant == true_term;
        // Constant-discharge tautology: (cl true) / (cl (not false)).
        let constant_taut = if positive {
            cx.chain
                .add_rule_step(AletheRule::True, vec![true_term], Vec::new(), Vec::new())
        } else {
            self.plan_false_taut(cx)
        };
        let not_rebuilt = self.terms.mk_not_raw(rebuilt);
        let not_constant = self.terms.mk_not_raw(constant);
        // A := (cl (not R) folded): equiv_pos oriented so the x-side literal
        // stays POSITIVE for `true` (folded = x) and NEGATIVE for `false`
        // (folded = (not x), emitted as the folded term itself).
        let (a_rule, a_clause) = match (x_first, positive) {
            (true, true) => (AletheRule::EquivPos1, vec![not_rebuilt, x, not_constant]),
            (false, true) => (AletheRule::EquivPos2, vec![not_rebuilt, not_constant, x]),
            (true, false) => (AletheRule::EquivPos2, vec![not_rebuilt, folded, constant]),
            (false, false) => (AletheRule::EquivPos1, vec![not_rebuilt, constant, folded]),
        };
        let a_taut = cx
            .chain
            .add_rule_step(a_rule, a_clause, Vec::new(), Vec::new());
        let a_conclusion = if positive {
            vec![not_rebuilt, x]
        } else {
            vec![not_rebuilt, folded]
        };
        let a_id = cx
            .chain
            .add_resolution(a_conclusion.clone(), constant, a_taut, constant_taut);
        // B := (cl R (not folded)): equiv_neg1 for `true` (negated conjuncts
        // (not x)/(not true)); equiv_neg2 for `false` (positive x/false —
        // the positive x literal IS `(not folded)` under decoding).
        let (b_rule, b_clause, b_conclusion) = if positive {
            let not_x = self.terms.mk_not(x);
            let clause = if x_first {
                vec![rebuilt, not_x, not_constant]
            } else {
                vec![rebuilt, not_constant, not_x]
            };
            (AletheRule::EquivNeg1, clause, vec![rebuilt, not_x])
        } else {
            let clause = if x_first {
                vec![rebuilt, x, constant]
            } else {
                vec![rebuilt, constant, x]
            };
            (AletheRule::EquivNeg2, clause, vec![rebuilt, x])
        };
        let b_taut = cx
            .chain
            .add_rule_step(b_rule, b_clause, Vec::new(), Vec::new());
        let b_id = cx
            .chain
            .add_resolution(b_conclusion.clone(), constant, b_taut, constant_taut);
        // Outer equivalence E = (= R folded).
        let equality = self
            .terms
            .mk_app(Symbol::named("="), [rebuilt, folded], Sort::Bool);
        let not_folded_literal = if positive { self.terms.mk_not(x) } else { x };
        let neg2 = cx.chain.add_rule_step(
            AletheRule::EquivNeg2,
            vec![equality, rebuilt, folded],
            Vec::new(),
            Vec::new(),
        );
        let r1 = cx
            .chain
            .add_resolution(vec![equality, folded], rebuilt, neg2, a_id);
        let not_equality_folded = self.terms.mk_not_raw(folded);
        let neg1 = cx.chain.add_rule_step(
            AletheRule::EquivNeg1,
            vec![equality, not_rebuilt, not_equality_folded],
            Vec::new(),
            Vec::new(),
        );
        let r2 = cx
            .chain
            .add_resolution(vec![equality, not_folded_literal], rebuilt, neg1, b_id);
        Some(cx.chain.add_resolution(vec![equality], folded, r1, r2))
    }

    fn plan_closed_fold_evaluation(
        &mut self,
        cx: &mut PlanCx<'_>,
        rebuilt: TermId,
        new_args: &[TermId],
        equality: TermId,
    ) -> ProofId {
        let arithmetic_only = matches!(
            self.terms.sort(rebuilt),
            Sort::Bool | Sort::Int | Sort::Real
        ) && new_args
            .iter()
            .all(|&arg| matches!(self.terms.sort(arg), Sort::Bool | Sort::Int | Sort::Real));
        if arithmetic_only {
            return cx.chain.add_rule_step(
                AletheRule::Evaluate,
                vec![equality],
                Vec::new(),
                Vec::new(),
            );
        }
        if cx.closed_bv_bitblast_bridge {
            return cx.chain.add_step(ProofStep::TheoryLemma {
                theory: "theory".to_owned(),
                clause: vec![equality],
                farkas: None,
                kind: TheoryLemmaKind::BvBitBlast,
                lia: None,
            });
        }
        // The strict `evaluate` BV fragment is concat-only. Use the bounded
        // BvLiaTautology re-proof and propositional double-negation strip from
        // `emit_forall_inst_unit_chain`; both are independently re-proved by
        // the untouched checker.
        let negated = self.terms.mk_not_raw(equality);
        let double_negated = self.terms.mk_not_raw(negated);
        let lemma = cx.chain.add_step(ProofStep::TheoryLemma {
            theory: "theory".to_owned(),
            clause: vec![double_negated],
            farkas: None,
            kind: TheoryLemmaKind::BvLiaTautology,
            lia: None,
        });
        let triple_negated = self.terms.mk_not_raw(double_negated);
        let strip = cx.chain.add_step(ProofStep::TheoryLemma {
            theory: "theory".to_owned(),
            clause: vec![triple_negated, equality],
            farkas: None,
            kind: TheoryLemmaKind::BoolTautology,
            lia: None,
        });
        cx.chain
            .add_resolution(vec![equality], double_negated, lemma, strip)
    }
}
