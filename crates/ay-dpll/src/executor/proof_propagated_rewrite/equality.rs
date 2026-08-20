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
                // A unit-propagation entry (#4751) is licensed by a bare unit
                // asserting `t`'s COMPLEMENT, not by a defining equality
                // `(= t false)`, so the source term is NOT the equality this
                // arm's contract returns. Derive that equality explicitly;
                // any other shape falls through to the unchanged path.
                if let Some(res) = self.plan_unit_literal_false_eq(cx, t, value, source) {
                    return Some(res);
                }
                // …and if that bridge does not apply, a `false`-valued entry
                // whose source is not the `(= t false)` defining equality has
                // NO license this arm can spell. Handing the source back as
                // `eq_term` would emit an `equiv_pos` step over a non-equality
                // — rejected by the strict checker, but better declined here.
                // Inert for every equality-harvesting producer, whose sources
                // are `(= expr value)` by construction.
                if value == self.terms.false_term() && !self.is_defining_equality(source, t, value)
                {
                    return None;
                }
                let id = self.plan_derive_clause(cx, source)?;
                return self.plan_compose_entry_value(cx, t, value, source, id, stamp);
            }
        }
        match self.terms.get(t).clone() {
            TermData::Const(_) | TermData::Var(_, _) => Some(EqRes::Unchanged),
            // The pass passes binders through unchanged.
            TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                Some(EqRes::Unchanged)
            }
            // A rewritten `not` child is replayed as a unary congruence
            // (#4751). Declining here was the sole reason a substituted CHC
            // transition relation could not be bridged back to its authored
            // root, which demoted the assume to a premiseless `trust` and
            // cost the whole refutation its strict presentation.
            TermData::Not(inner) => match self.plan_derive_eq(cx, inner, stamp)? {
                EqRes::Unchanged => Some(EqRes::Unchanged),
                EqRes::Changed { to, id, .. } => {
                    cx.spend(1)?;
                    let rebuilt = self.terms.mk_not(to);
                    // `mk_not` may fold (double negation, a constant child).
                    // The congruence conclusion is then NOT `(not to)`, so
                    // this slice declines rather than emit a step the strict
                    // checker would have to take on faith.
                    match self.terms.get(rebuilt) {
                        TermData::Not(rebuilt_inner) if *rebuilt_inner == to => {}
                        _ => return None,
                    }
                    let eq_term = self
                        .terms
                        .mk_app(Symbol::named("="), [t, rebuilt], Sort::Bool);
                    let cong_id = cx.chain.add_rule_step(
                        AletheRule::Cong,
                        vec![eq_term],
                        vec![id],
                        Vec::new(),
                    );
                    Some(EqRes::Changed {
                        to: rebuilt,
                        eq_term,
                        id: cong_id,
                    })
                }
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

    /// Compose an entry's replacement with the entries that license ITS
    /// subterms (#4751 `_mod_q` class).
    ///
    /// `VariableSubstitution::substitute_term` applies the pass's map to
    /// FIXPOINT, so a replacement can itself mention a substituted variable:
    /// the CHC Euclidean decomposition `(= x (+ (* k q) r))` yields the entry
    /// `x |-> (+ (* k q) r)` while the pass, seeing `r |-> 0` as well,
    /// actually writes `(* k q)`. Returning the entry's replacement verbatim
    /// therefore reconstructed a term the pass never produced, and the record
    /// bridge declined on the mismatch — measured on `dillig12_m` as the
    /// dominant decline (`to=(<= -1 (+ (+ (* _mod_q_0 2) _mod_r_1) -1))` for a
    /// recorded `after=(<= -1 (+ (* _mod_q_0 2) -1))`).
    ///
    /// Replay the replacement and, when it changes, chain the two equalities
    /// with `trans`. `trans` is validated by an UNDIRECTED path search
    /// (`euf_step_rules::validate_trans`), so the licensing equality's
    /// orientation — `(= t value)` or `(= value t)` — does not matter, but the
    /// conclusion must still be the exact `(= t to)` node, which is verified
    /// structurally because `mk_app` may fold. Any decline leaves the caller
    /// with today's fail-closed behaviour.
    fn plan_compose_entry_value(
        &mut self,
        cx: &mut PlanCx<'_>,
        t: TermId,
        value: TermId,
        source: TermId,
        source_id: ProofId,
        stamp: u32,
    ) -> Option<EqRes> {
        let unchanged = || {
            Some(EqRes::Changed {
                to: value,
                eq_term: source,
                id: source_id,
            })
        };
        // Every leg falls back to the UNCOMPOSED result, never to `None`:
        // this arm must be purely additive, or a plan that succeeds today
        // could start declining.
        let Some(EqRes::Changed {
            to, id: inner_id, ..
        }) = self.plan_derive_eq(cx, value, stamp)
        else {
            return unchanged();
        };
        // A composed value that lands back on `t` (or on `value`) gives
        // `trans` no two-edge path to validate.
        if to == t || to == value {
            return unchanged();
        }
        if cx.spend(1).is_none() {
            return unchanged();
        }
        let final_eq = self.terms.mk_app(Symbol::named("="), [t, to], Sort::Bool);
        match self.terms.get(final_eq) {
            TermData::App(symbol, args) if symbol.name() == "=" && args.as_slice() == [t, to] => {}
            _ => return unchanged(),
        }
        let final_id = cx.chain.add_rule_step(
            AletheRule::Trans,
            vec![final_eq],
            vec![source_id, inner_id],
            Vec::new(),
        );
        Some(EqRes::Changed {
            to,
            eq_term: final_eq,
            id: final_id,
        })
    }

    /// Whether `source` is spelled `(= expr value)` or `(= value expr)` — the
    /// shape [`PropagateValues::extract_value_equality`] harvests entries
    /// from, and therefore the shape the entry arm may return as its
    /// `eq_term`.
    fn is_defining_equality(&self, source: TermId, expr: TermId, value: TermId) -> bool {
        match self.terms.get(source) {
            TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2 => {
                (args[0] == expr && args[1] == value) || (args[0] == value && args[1] == expr)
            }
            _ => false,
        }
    }

    /// Derive `(cl (= t false))` from a unit asserting `t`'s complement
    /// (#4751 — top-level unit propagation).
    ///
    /// `PropagateValues` harvests `expr ↦ value` from a defining EQUALITY, so
    /// [`Self::plan_derive_eq_inner`] may hand that source term straight back
    /// as the licensing equality. Unit propagation instead deletes a disjunct
    /// `t` because a bare unit `u` asserting `t`'s complement is on the stack,
    /// so the equality has to be BUILT:
    ///
    /// ```text
    ///   (cl (= t false) t false)      :rule equiv_neg2
    ///   (cl (= t false) false)        resolve with (cl u) on t's atom
    ///   (cl (not false))              :rule false
    ///   (cl (= t false))              resolve on false
    /// ```
    ///
    /// Every step is re-derived by the UNTOUCHED strict checker, and the
    /// licensing unit itself must be derivable from authored roots
    /// (`plan_derive_clause`). Returns `None` — leaving the caller's existing
    /// behaviour byte-identical — unless the value really is literal `false`
    /// and `source` really is the literal complement of `t`.
    fn plan_unit_literal_false_eq(
        &mut self,
        cx: &mut PlanCx<'_>,
        t: TermId,
        value: TermId,
        source: TermId,
    ) -> Option<EqRes> {
        let false_term = self.terms.false_term();
        if value != false_term || t == false_term || t == source {
            return None;
        }
        let complementary = match self.terms.get(t) {
            TermData::Not(inner) => *inner == source,
            _ => matches!(self.terms.get(source), TermData::Not(inner) if *inner == t),
        };
        if !complementary {
            return None;
        }
        cx.spend(4)?;
        let source_id = self.plan_derive_clause(cx, source)?;
        let eq_term = self
            .terms
            .mk_app(Symbol::named("="), [t, false_term], Sort::Bool);
        let taut = cx.chain.add_rule_step(
            AletheRule::EquivNeg2,
            vec![eq_term, t, false_term],
            Vec::new(),
            Vec::new(),
        );
        let after_unit = cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![eq_term, false_term],
            vec![taut, source_id],
            Vec::new(),
        );
        let false_taut = self.plan_false_taut(cx);
        let id = cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![eq_term],
            vec![after_unit, false_taut],
            Vec::new(),
        );
        Some(EqRes::Changed {
            to: false_term,
            eq_term,
            id,
        })
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
        let mut folded =
            PropagateValues::fold_rebuild(self.terms, symbol.clone(), term, new_args.clone());
        // Mirror `rewrite`'s post-fold map lookup.
        let mut tail = cx
            .entry_by_expr
            .get(&folded)
            .copied()
            .filter(|&(_, _, entry_stamp)| entry_stamp <= stamp);
        if tail.map_or(folded, |(value, _, _)| value) == term {
            return Some(EqRes::Unchanged);
        }
        let mut bridge =
            self.plan_fold_bridge(cx, term, folded, &symbol, &args, &new_args, &child_results);
        if bridge.is_none() {
            // Producer-model fallback (#4751). `fold_rebuild` models the
            // `PropagateValues` pass, which rebuilds boolean connectives
            // through `mk_and`/`mk_or` and therefore DROPS unit conjuncts:
            // an 8-ary `and` whose two substituted atoms folded to `true`
            // comes back 6-ary. `VariableSubstitution` rebuilds the same node
            // structurally and keeps all 8, so the folding model cannot
            // reconstruct the term that pass actually produced. Retry with
            // the structural rebuild.
            //
            // This cannot admit anything: the retry only supplies a different
            // CANDIDATE target, and it still has to be reached by a
            // congruence whose every argument pair is discharged by a derived
            // child equality, then still has to equal the recorded `after` at
            // the bridge, then still has to survive the strict checker. A
            // wrong candidate simply declines, exactly as before.
            let sort = self.terms.sort(term).clone();
            let structural = self.terms.mk_app(symbol.clone(), new_args.clone(), sort);
            if structural != folded {
                let retry_tail = cx
                    .entry_by_expr
                    .get(&structural)
                    .copied()
                    .filter(|&(_, _, entry_stamp)| entry_stamp <= stamp);
                if retry_tail.map_or(structural, |(value, _, _)| value) != term {
                    bridge = self.plan_fold_bridge(
                        cx,
                        term,
                        structural,
                        &symbol,
                        &args,
                        &new_args,
                        &child_results,
                    );
                    if bridge.is_some() {
                        folded = structural;
                        tail = retry_tail;
                    }
                }
            }
        }
        let (eq_term, id) = bridge?;
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
                .plan_linear_identity_fold(cx, term, folded, symbol, args, new_args, child_results)
                .or_else(|| {
                    self.plan_collapsing_fold(
                        cx,
                        term,
                        folded,
                        symbol,
                        args,
                        new_args,
                        child_results,
                    )
                })
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
                })
                .or_else(|| {
                    self.plan_arith_normalization_fold(
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

    /// Arithmetic-identity collapsing fold (#4751 `_mod_q` class).
    ///
    /// [`Self::plan_collapsing_fold`] closes a fold only when EVERY rebuilt
    /// argument is a constant, because its bridge is a ground `evaluate`. The
    /// substitution folds this class needs are not ground: replacing the
    /// dividend of a Euclidean decomposition turns `(+ x -1)` into
    /// `(+ (+ (* q 2) 0) -1)`, which the term store rebuilds as
    /// `(+ (* q 2) -1)` — an ADDITIVE-IDENTITY/flattening fold over a term
    /// that still mentions `q`.
    ///
    /// Bridge it with the checker's own linear-identity theorem:
    ///
    /// ```text
    ///   cong             (= term rebuilt)     premises: the child equalities
    ///   lia_generic      (= rebuilt folded)   LiaAnnotation::LinearIdentity
    ///   trans            (= term folded)
    /// ```
    ///
    /// SOUNDNESS. The middle step is admitted ONLY when
    /// `ay_core::proof_validation::recognize_lia_linear_identity` accepts it,
    /// which is the exact inverse of the `validate_linear_identity` the strict
    /// checker runs: `rebuilt - folded` must reduce to the identically-zero
    /// INTEGER linear form, so the equality holds in every model. A nonlinear
    /// or Real-tainted subterm only PREVENTS recognition (the normalizer
    /// treats it as an opaque atom and any residual coefficient fails the
    /// zero test), so this can never accept a non-identity. `cong` and `trans`
    /// are unchanged rules with every premise discharged, and the whole chain
    /// is replayed by the UNTOUCHED strict checker before the proof is
    /// accepted. Every guard below fails CLOSED to today's demotion.
    fn plan_linear_identity_fold(
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
        if !matches!(sort, Sort::Int) || !matches!(self.terms.sort(folded), Sort::Int) {
            return None;
        }
        cx.spend(2)?;
        let rebuilt = self.terms.mk_app(symbol.clone(), new_args, sort);
        if rebuilt == term || rebuilt == folded {
            return None;
        }
        // `mk_app` may normalize; the congruence conclusion must name the
        // node the premises actually build.
        match self.terms.get(rebuilt) {
            TermData::App(rebuilt_symbol, rebuilt_args)
                if rebuilt_symbol == symbol && rebuilt_args.as_slice() == new_args => {}
            _ => return None,
        }
        let identity = self
            .terms
            .mk_app(Symbol::named("="), [rebuilt, folded], Sort::Bool);
        match self.terms.get(identity) {
            TermData::App(identity_symbol, identity_args)
                if identity_symbol.name() == "="
                    && identity_args.as_slice() == [rebuilt, folded] => {}
            _ => return None,
        }
        if !ay_core::proof_validation::recognize_lia_linear_identity(self.terms, &[identity]) {
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
        let lemma = cx.chain.add_step(ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![identity],
            // The strict checker validates through the `LinearIdentity`
            // annotation; the Alethe printer additionally wants one Farkas
            // coefficient per literal to render `lia_generic` (#8821).
            farkas: Some(ay_core::FarkasAnnotation::new(vec![
                num_rational::Rational64::from(1),
            ])),
            kind: TheoryLemmaKind::LiaGeneric,
            lia: Some(ay_core::LiaAnnotation::LinearIdentity),
        });
        let term_to_folded = self
            .terms
            .mk_app(Symbol::named("="), [term, folded], Sort::Bool);
        let transitivity = cx.chain.add_rule_step(
            AletheRule::Trans,
            vec![term_to_folded],
            vec![congruence, lemma],
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

    /// Arithmetic-normalization bridge (#4751).
    ///
    /// `VariableSubstitution` rebuilds arithmetic nodes through the CANONICAL
    /// constructors (`mk_add`/`mk_sub`/`mk_mul`), which re-associate,
    /// distribute and collect like terms. Congruence alone reaches only the
    /// RAW rebuild, so the two spellings diverge and the chain cannot reach
    /// the recorded `after`. Measured on the dillig12_m CHC benchmark:
    /// substituting `A := B` in `(+ A B)` gives raw `(+ B B)` where the pass
    /// stores `(* B 2)`, and `C := (+ A 2)` in `(* C -2)` gives raw
    /// `(* (+ A 2) -2)` where the pass stores `(+ (* A -2) -4)`.
    ///
    /// Neither shape is expressible as substitution-plus-constant-fold, so
    /// this slice bridges the two spellings with ONE rule the strict checker
    /// ALREADY validates independently: an `LraFarkas` theory lemma
    /// `(cl (= raw canonical))` carrying the unit coefficient. The checker's
    /// Farkas validator linearizes both sides ITSELF and accepts only when
    /// the single disequality row cancels to a contradiction in both
    /// orientations - that is, only when the two terms are the SAME linear
    /// polynomial. It rejects `(= (+ B B) (* B 3))`, `(= (+ B C) (* B 2))`
    /// and every non-linear pair, so no identity is taken on trust and no
    /// checker rule is added or widened.
    ///
    /// Fail-closed: the SAME public validator runs at PLAN time on the exact
    /// literal about to be emitted, so a pair the checker would reject
    /// declines here and the assume keeps today's demotion behaviour rather
    /// than splicing a step that would fail the whole presentation.
    fn plan_arith_normalization_fold(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        symbol: &Symbol,
        args: &[TermId],
        new_args: &[TermId],
        child_results: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        // Only the arithmetic constructors renormalize; every other head
        // rebuilds structurally and is already covered by the shape arms.
        if !matches!(symbol.name(), "+" | "-" | "*") {
            return None;
        }
        let sort = self.terms.sort(term).clone();
        if !matches!(sort, Sort::Int | Sort::Real) {
            return None;
        }
        let rebuilt = self.terms.mk_app(symbol.clone(), new_args, sort.clone());
        if rebuilt == term || rebuilt == folded {
            return None;
        }
        let premises = Self::congruence_premises(args, child_results, new_args)?;
        let rebuilt_to_folded =
            self.terms
                .mk_app(Symbol::named("="), [rebuilt, folded], Sort::Bool);
        if !Self::linear_identity_holds(self.terms, rebuilt_to_folded) {
            return None;
        }
        cx.spend(3)?;
        let term_to_rebuilt = self
            .terms
            .mk_app(Symbol::named("="), [term, rebuilt], Sort::Bool);
        let congruence = cx.chain.add_rule_step(
            AletheRule::Cong,
            vec![term_to_rebuilt],
            premises,
            Vec::new(),
        );
        let theory = if sort == Sort::Int { "LIA" } else { "LRA" };
        let normalization = cx.chain.add_theory_lemma_with_farkas_and_kind(
            theory,
            vec![rebuilt_to_folded],
            ay_core::FarkasAnnotation::from_ints(&[1]),
            TheoryLemmaKind::LraFarkas,
        );
        let term_to_folded = self
            .terms
            .mk_app(Symbol::named("="), [term, folded], Sort::Bool);
        let transitivity = cx.chain.add_rule_step(
            AletheRule::Trans,
            vec![term_to_folded],
            vec![congruence, normalization],
            Vec::new(),
        );
        Some((term_to_folded, transitivity))
    }

    /// Whether the strict checker's own Farkas validator proves the unit
    /// clause `(cl equality)` from the unit coefficient - i.e. whether the
    /// equality's two sides are the same linear polynomial.
    ///
    /// This is the EXACT call `lra_farkas`'s strict validator makes for a
    /// single-disequality row (`verify_farkas_conflict_lits_full`), so a plan
    /// accepted here is accepted there and a plan rejected here would have
    /// been rejected there.
    pub(super) fn linear_identity_holds(terms: &TermStore, equality: TermId) -> bool {
        ay_core::proof_validation::verify_farkas_conflict_lits_full(
            terms,
            &[ay_core::TheoryLit::new(equality, false)],
            &ay_core::FarkasAnnotation::from_ints(&[1]),
        )
        .is_ok()
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
