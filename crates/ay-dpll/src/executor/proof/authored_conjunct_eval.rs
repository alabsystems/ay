// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Record the argument behind a preprocessor fold-to-`false`.
//!
//! ## The defect
//!
//! When preprocessing itself refutes an authored assertion it REWRITES that
//! slot in the live `ctx.assertions` stack to the constant `false` and keeps
//! no derivation for the rewrite. Everything downstream then sees a proof
//! whose only leaf is `assume false`, which proves `false |- bottom` — nothing
//! about the input — so `false_source::demote_unattributed_assumed_false`
//! erases the whole document down to `(step t0 (cl) :rule hole)`. That
//! erasure is correct and must stay. What it CONCEALS is the real defect: the
//! solver derived a refutation and threw the argument away. This is the
//! pigeonhole shape, and the remedy is the same one
//! `rebuild_finite_enum_pigeonhole_refutation` applies there — RECORD it.
//!
//! ## Why the argument is recoverable
//!
//! The fold fires because one conjunct of the authored assertion is false on
//! its own, by evaluation. Measured on QF_DT `barrett-jsat/typed` at
//! 800b0668e:
//!
//! ```text
//! typed_v2l20006  (assert (and (not ((_ is leaf) (leaf x1))) (not (= x3 x4))))
//! typed_v1l20003  (assert (and (not (= (ite ...) x1)) (not ((_ is cons) (cons (leaf x1) null)))))
//! typed_v1l80035  (assert (and (and ... (not (= (succ zero) (succ zero)))) ...))
//! ```
//!
//! Each carries a conjunct `(not X)` where `X` is either syntactic
//! reflexivity (`(= t t)`) or a declaration-backed datatype evaluation (a
//! tester applied to a term literally built with that constructor, or a
//! selector applied to its own constructor). Both are things AY's strict
//! checker already validates against the problem's own `declare-datatypes`.
//!
//! So the derivation is: assume the authored root, project the conjunct out
//! with strictly-validated `and_pos` + resolution, discharge it, resolve.
//!
//! ```text
//! (assume h0 (and (not (is-leaf (leaf x1))) (not (= x3 x4))))
//! (step t1 (cl (not <root>) (not (is-leaf (leaf x1)))) :rule and_pos)
//! (step t2 (cl (not (is-leaf (leaf x1)))) :rule resolution :premises (t1 h0))
//! (step t3 (cl (is-leaf (leaf x1))) :rule dt_tester)
//! (step t4 (cl) :rule resolution :premises (t2 t3))
//! ```
//!
//! ## What this is NOT
//!
//! It does not weaken the poison, the `assume false` erasure, or any gate. It
//! runs only where the alternative is a one-line hole, it commits only a
//! candidate the UNCHANGED strict checker accepts whole, and its single
//! `assume` is the author's own assertion re-interned RAW from the parsed
//! surface (never a normalized re-elaboration, which is how the folded
//! constant got in). Any failure leaves the erasure exactly as it was.
//!
//! On the wire `dt_tester`/`dt_project` are not checkable Alethe rules, so
//! those steps print as `hole` and carcara reports `holey`, not `valid`. That
//! is the honest state of the art: Alethe has no datatype rules. The
//! difference from today is the whole point — the artifact now NAMES the one
//! obligation it cannot discharge and derives everything around it from the
//! author's assertion, instead of asserting an empty clause from nothing.
//! Reflexivity closes with `eq_reflexive`, which IS checkable.

use super::*;

/// Upper bound on conjunct nodes inspected per authored root. The scan is
/// linear in the raw `and`-tree, which `raw_intern_surface` has already
/// bounded per root; this is a second, independent stop so a pathological
/// tree cannot turn a bounded root into an unbounded search.
const MAX_SCANNED_CONJUNCT_NODES: usize = 8_192;

/// How a self-false conjunct is discharged.
#[derive(Clone, Copy)]
enum ConjunctEvalCloser {
    /// `(= t t)` with SYNTACTICALLY identical sides — Alethe `eq_reflexive`.
    Reflexivity,
    /// A declaration-backed datatype evaluation.
    Datatype(TheoryLemmaKind),
    /// A unit theory lemma one of `ay-proof`'s OWN recognizers accepts.
    ///
    /// The recognizer consulted here is the exact precondition of the strict
    /// validator that will re-run on the committed lemma, so this can only
    /// name a kind strict mode then re-derives independently (array
    /// read-over-write chain evaluation, ground string/regex evaluation). The
    /// `&'static str` is the `theory` tag the lemma carries on the wire.
    TheoryLemma(&'static str, TheoryLemmaKind),
}

impl Executor {
    /// Replace a proof that rests on an unattributed `assume false` with the
    /// derivation the preprocessor's fold actually had. `true` when a
    /// strictly-checked replacement was committed.
    pub(super) fn replace_with_exact_authored_conjunct_eval_refutation(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        // Two traversals of the parsed stack: the deep clone below, and the
        // raw re-intern. Charged against the SAME query-local envelope every
        // other source-touching pass shares, so this pass cannot spend work
        // the aggregate ceiling has not authorized (and an unbounded root
        // fails closed here exactly as it does at the build preflight).
        if !self.proof_source_work.spend(
            crate::executor::proof_repair::proof_trust_surgery_surface_audit::ProofSourcePass::AuthoredConjunctEvalRebuild,
            self.ctx.assertions_parsed(),
        ) {
            return false;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        if parsed.is_empty() {
            return false;
        }
        let datatype_decls = self.datatype_decls_for_strict_proof();
        let selector_decls = self.ctor_selector_decls_for_strict_proof();
        for assertion in &parsed {
            if self.try_authored_conjunct_eval_refutation(
                proof,
                assertion,
                &datatype_decls,
                &selector_decls,
            ) {
                return true;
            }
        }
        false
    }

    fn try_authored_conjunct_eval_refutation(
        &mut self,
        proof: &mut Proof,
        assertion: &FrontendTerm,
        datatype_decls: &[(String, Vec<String>)],
        selector_decls: &[(String, Vec<String>)],
    ) -> bool {
        // Only an application can carry conjuncts, and `raw_intern_surface`
        // fails closed on anything it cannot rebuild node-by-node.
        if !matches!(
            crate::executor::proof_surface_syntax::strip_frontend_annotations(assertion),
            FrontendTerm::App(..)
        ) {
            return false;
        }
        let Some(root) = self.raw_intern_surface(assertion) else {
            return false;
        };
        if !self.rebuilt_root_prints_as_authored(root, assertion) {
            return false;
        }
        let Some(nodes) = self.raw_and_tree_leaves(root) else {
            return false;
        };
        for (leaf, path) in &nodes {
            // Two polarities of the SAME argument.
            //
            // NEGATED leaf `(not X)`: discharge proves `X`, and the conjunct
            // supplies `(not X)` — the original shape.
            //
            // POSITIVE leaf `L`: the conjunct supplies `L` and the discharge
            // has to prove `(not L)`. A fold-to-`false` reaches this form
            // whenever the author wrote the false claim directly rather than
            // negated — `(assert (= (str.++ "a" "b") "ac"))` — which the
            // `(not X)`-only scan skipped entirely, so those queries lost the
            // whole document to `(step t0 (cl) :rule hole)`. The pivot and the
            // resolution operand order are the mirror image; nothing else
            // changes, and the strict checker remains the only commit
            // authority for either polarity.
            let negated_inner = match self.ctx.terms.get(*leaf) {
                TermData::Not(inner) => Some(*inner),
                _ => None,
            };
            let (inner, negated_leaf) = match negated_inner {
                Some(inner) => (inner, true),
                None => (self.ctx.terms.mk_not_raw(*leaf), false),
            };
            let Some(closer) = self.conjunct_eval_closer(inner, datatype_decls, selector_decls)
            else {
                // A negated implication is one NNF step away from two more
                // conjuncts; the closers themselves stay leaf-only.
                if self.try_authored_not_implies_conjunct_refutation(
                    proof,
                    root,
                    path,
                    *leaf,
                    datatype_decls,
                    selector_decls,
                ) {
                    return true;
                }
                continue;
            };
            let mut candidate = Proof::new();
            let assume_id = candidate.add_assume(root, None);
            let Some(unit) = Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                &mut candidate,
                assume_id,
                root,
                path,
                *leaf,
            ) else {
                continue;
            };
            let discharge = Self::emit_conjunct_eval_discharge(&mut candidate, inner, closer);
            // `add_resolution(clause, pivot, c1, c2)` wants the premise
            // carrying the pivot's NEGATIVE occurrence first. For a negated
            // leaf the pivot is `inner` and the unit `(cl (not inner))` holds
            // it; for a positive leaf the pivot is the leaf itself and the
            // DISCHARGE `(cl (not leaf))` holds it.
            if negated_leaf {
                candidate.add_resolution(Vec::new(), inner, unit, discharge);
            } else {
                candidate.add_resolution(Vec::new(), *leaf, discharge, unit);
            }
            // The UNCHANGED strict checker is the only authority that commits
            // this. It re-derives `and_pos` positionally, re-checks
            // reflexivity syntactically, and re-validates the datatype step
            // against the problem's own declarations.
            if Self::proof_derives_empty_clause(&candidate)
                && self.check_proof_strict_with_datatypes(&candidate).is_ok()
            {
                *proof = candidate;
                // `root` is the author's assertion re-interned raw from its
                // parsed surface; record it so the export authority accepts
                // the rebuilt `assume` without granting any generated leaf.
                self.record_rebuilt_authored_proof_premise(root);
                return true;
            }
        }
        self.try_authored_bound_pair_refutation(proof, root, &nodes)
    }

    /// A conjunct leaf `(not (=> F1 F2))` holds two more conjuncts one NNF
    /// step away: `F1` and `(not F2)`. The `and`-tree scan cannot descend
    /// into it (it is not an `and`), so a fold like
    /// `(assert (not (=> hyp (= (select (store s 1 w) 1) w))))` — the shape
    /// the nested-array proof-authority test pins — lost the whole document
    /// to a bare hole even though the consequent alone is a ROW tautology
    /// every closer already recognises. Unfold exactly one level with the
    /// strictly-validated `not_implies1`/`not_implies2` Alethe rules and
    /// retry the SAME closers on each side; the UNCHANGED strict checker
    /// remains the only commit authority. The desugared binary
    /// `(not (or (not F1) F2))` form is admitted because the `not_implies`
    /// validators accept it by the same reading.
    fn try_authored_not_implies_conjunct_refutation(
        &mut self,
        proof: &mut Proof,
        root: TermId,
        path: &[u32],
        leaf: TermId,
        datatype_decls: &[(String, Vec<String>)],
        selector_decls: &[(String, Vec<String>)],
    ) -> bool {
        let TermData::Not(implication) = self.ctx.terms.get(leaf) else {
            return false;
        };
        let (antecedent, consequent) = match self.ctx.terms.get(*implication) {
            TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
                (args[0], args[1])
            }
            TermData::App(Symbol::Named(name), args) if name == "or" && args.len() == 2 => {
                let TermData::Not(first) = self.ctx.terms.get(args[0]) else {
                    return false;
                };
                (*first, args[1])
            }
            _ => return false,
        };

        // Consequent branch: `not_implies2` derives `(cl (not F2))`; the
        // discharge proves `(cl F2)`.
        let not_consequent = self.ctx.terms.mk_not_raw(consequent);
        if let Some(closer) = self.conjunct_eval_closer(consequent, datatype_decls, selector_decls)
        {
            let mut candidate = Proof::new();
            let assume_id = candidate.add_assume(root, None);
            if let Some(unit) = Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                &mut candidate,
                assume_id,
                root,
                path,
                leaf,
            ) {
                let derived = candidate.add_rule_step(
                    AletheRule::NotImplies2,
                    vec![not_consequent],
                    vec![unit],
                    Vec::new(),
                );
                let discharge =
                    Self::emit_conjunct_eval_discharge(&mut candidate, consequent, closer);
                candidate.add_resolution(Vec::new(), consequent, derived, discharge);
                if Self::proof_derives_empty_clause(&candidate)
                    && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                {
                    *proof = candidate;
                    self.record_rebuilt_authored_proof_premise(root);
                    return true;
                }
            }
        }

        // Antecedent branch: `not_implies1` derives `(cl F1)`; the discharge
        // proves `(cl (not F1))`.
        let not_antecedent = self.ctx.terms.mk_not_raw(antecedent);
        if let Some(closer) =
            self.conjunct_eval_closer(not_antecedent, datatype_decls, selector_decls)
        {
            let mut candidate = Proof::new();
            let assume_id = candidate.add_assume(root, None);
            if let Some(unit) = Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                &mut candidate,
                assume_id,
                root,
                path,
                leaf,
            ) {
                let derived = candidate.add_rule_step(
                    AletheRule::NotImplies1,
                    vec![antecedent],
                    vec![unit],
                    Vec::new(),
                );
                let discharge =
                    Self::emit_conjunct_eval_discharge(&mut candidate, not_antecedent, closer);
                candidate.add_resolution(Vec::new(), antecedent, discharge, derived);
                if Self::proof_derives_empty_clause(&candidate)
                    && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                {
                    *proof = candidate;
                    self.record_rebuilt_authored_proof_premise(root);
                    return true;
                }
            }
        }
        false
    }

    /// The single closer-discharge step `(cl proposition)`, shared by the
    /// direct-leaf and `not_implies` paths.
    fn emit_conjunct_eval_discharge(
        candidate: &mut Proof,
        proposition: TermId,
        closer: ConjunctEvalCloser,
    ) -> ProofId {
        match closer {
            ConjunctEvalCloser::Reflexivity => candidate.add_rule_step(
                AletheRule::EqReflexive,
                vec![proposition],
                Vec::new(),
                Vec::new(),
            ),
            ConjunctEvalCloser::Datatype(kind) => {
                candidate.add_theory_lemma_with_kind("datatype", vec![proposition], kind)
            }
            ConjunctEvalCloser::TheoryLemma(theory, kind) => {
                candidate.add_theory_lemma_with_kind(theory, vec![proposition], kind)
            }
        }
    }

    /// Second closer family: a PAIR of arithmetic conjuncts whose unit-weight
    /// Farkas combination contradicts (`x <= 6` with `x > 10` — the shape a
    /// bound-propagation fold collapses to `false` without recording its
    /// derivation). One `and_pos` chain per participating conjunct, one
    /// `LiaGeneric` Farkas lemma over their negations, two resolutions to the
    /// empty clause. The UNCHANGED strict checker (its `lia::validate_metered`
    /// farkas route) is still the only commit authority: a pair whose [1, 1]
    /// combination does not actually contradict simply fails the check and the
    /// erasure proceeds as before, so this can never certify anything the
    /// checker would not independently accept.
    fn try_authored_bound_pair_refutation(
        &mut self,
        proof: &mut Proof,
        root: TermId,
        nodes: &[(TermId, Vec<u32>)],
    ) -> bool {
        /// Bound the candidate-pair search: the folds this recovers come from
        /// tiny per-clause bodies, and each candidate runs a strict check.
        const MAX_ARITHMETIC_LEAVES: usize = 16;
        fn is_comparison(terms: &TermStore, term: TermId) -> bool {
            matches!(
                terms.get(term),
                TermData::App(Symbol::Named(name), args)
                    if args.len() == 2
                        && matches!(name.as_str(), "<" | "<=" | ">" | ">=")
            )
        }
        // A leaf participates either as a direct comparison (`x > 10`) or as a
        // negated one (`(not (>= x 5))` — how a folded upper bound usually
        // appears). Track the polarity so each resolution places the pivot on
        // the side the checker's existing convention expects.
        let arithmetic: Vec<(TermId, &Vec<u32>, bool)> = nodes
            .iter()
            .filter_map(|(leaf, path)| {
                if is_comparison(&self.ctx.terms, *leaf) {
                    return Some((*leaf, path, false));
                }
                if let TermData::Not(inner) = self.ctx.terms.get(*leaf) {
                    if is_comparison(&self.ctx.terms, *inner) {
                        return Some((*leaf, path, true));
                    }
                }
                None
            })
            .take(MAX_ARITHMETIC_LEAVES)
            .collect();
        for (first_index, &(leaf_a, path_a, negated_a)) in arithmetic.iter().enumerate() {
            for &(leaf_b, path_b, negated_b) in arithmetic.iter().skip(first_index + 1) {
                let mut candidate = Proof::new();
                let assume_id = candidate.add_assume(root, None);
                let Some(unit_a) = Self::emit_and_pos_chain(
                    &mut self.ctx.terms,
                    &mut candidate,
                    assume_id,
                    root,
                    path_a,
                    leaf_a,
                ) else {
                    continue;
                };
                let Some(unit_b) = Self::emit_and_pos_chain(
                    &mut self.ctx.terms,
                    &mut candidate,
                    assume_id,
                    root,
                    path_b,
                    leaf_b,
                ) else {
                    continue;
                };
                // The lemma's blocking literal is the complement of the unit:
                // for a positive leaf `D` that is `(not D)` with pivot `D`;
                // for a negated leaf `(not C)` it is `C` itself with pivot
                // `C` — never a double negation.
                let (lemma_a, pivot_a) = if negated_a {
                    let TermData::Not(inner) = self.ctx.terms.get(leaf_a) else {
                        continue;
                    };
                    (*inner, *inner)
                } else {
                    (self.ctx.terms.mk_not_raw(leaf_a), leaf_a)
                };
                let (lemma_b, pivot_b) = if negated_b {
                    let TermData::Not(inner) = self.ctx.terms.get(leaf_b) else {
                        continue;
                    };
                    (*inner, *inner)
                } else {
                    (self.ctx.terms.mk_not_raw(leaf_b), leaf_b)
                };
                let lemma = candidate.add_theory_lemma_with_farkas_and_kind(
                    "LIA",
                    vec![lemma_a, lemma_b],
                    FarkasAnnotation::from_ints(&[1, 1]),
                    TheoryLemmaKind::LiaGeneric,
                );
                // Mirror the single-leaf convention: `add_resolution(clause,
                // pivot, c1, c2)` with the premise carrying the pivot's
                // NEGATIVE occurrence first.
                let partial = if negated_a {
                    candidate.add_resolution(vec![lemma_b], pivot_a, unit_a, lemma)
                } else {
                    candidate.add_resolution(vec![lemma_b], pivot_a, lemma, unit_a)
                };
                if negated_b {
                    candidate.add_resolution(Vec::new(), pivot_b, unit_b, partial);
                } else {
                    candidate.add_resolution(Vec::new(), pivot_b, partial, unit_b);
                }
                if Self::proof_derives_empty_clause(&candidate)
                    && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                {
                    *proof = candidate;
                    self.record_rebuilt_authored_proof_premise(root);
                    return true;
                }
            }
        }
        false
    }

    /// Whether the rebuilt root PRINTS BACK as the assertion the author wrote.
    ///
    /// This is not belt-and-braces; it is the difference between `holey` and
    /// `invalid`. A raw re-intern rebuilds the term node by node, but the store
    /// hash-conses, so a subterm the author wrote one way can share a `TermId`
    /// with a subterm written another way, and the printer's surface-override
    /// table then renders BOTH with whichever spelling it holds. Measured on a
    /// reduction of QF_DT `typed_v1l20003`, whose source contains
    /// `(ite ((_ is cons) null) (car null) (leaf zero))` — that whole `ite`
    /// folds to `(leaf zero)`, so the two share an id, and the rebuilt premise
    /// printed as
    ///
    /// ```text
    /// (and (not (= (ite ((_ is cons) null) (car null)
    ///                   (ite ((_ is cons) null) (car null) (leaf zero))))
    ///              (ite ((_ is cons) null) (car null) (leaf zero)))) ...)
    /// ```
    ///
    /// where the author wrote `(leaf zero)` in the last two positions. carcara:
    /// "could not match term to any of the original problem premises" —
    /// INVALID, the worst possible outcome, strictly worse than the one-line
    /// hole it replaced.
    ///
    /// So render the premise through the SAME override-aware printer the
    /// exporter uses, re-parse it, and require the result to be the author's
    /// own parsed assertion. Anything else declines and the erasure proceeds.
    pub(super) fn rebuilt_root_prints_as_authored(
        &self,
        root: TermId,
        assertion: &FrontendTerm,
    ) -> bool {
        let authored = crate::executor::proof_surface_syntax::strip_frontend_annotations(assertion);
        let overrides = self.proof_export_term_overrides().unwrap_or_default();
        let rendered =
            ay_proof::format_term_alethe_with_overrides(&self.ctx.terms, root, &overrides);
        parse_rendered_assertion(&rendered).is_some_and(|reparsed| {
            crate::executor::proof_surface_syntax::strip_frontend_annotations(&reparsed) == authored
        })
    }

    /// Every non-`and` node of the raw `and`-tree rooted at `root`, paired
    /// with the child-index path that reaches it. `None` when the tree is
    /// larger than the scan bound.
    fn raw_and_tree_leaves(&self, root: TermId) -> Option<Vec<(TermId, Vec<u32>)>> {
        let mut leaves: Vec<(TermId, Vec<u32>)> = Vec::new();
        let mut stack: Vec<(TermId, Vec<u32>)> = vec![(root, Vec::new())];
        let mut visited = 0usize;
        while let Some((term, path)) = stack.pop() {
            visited += 1;
            if visited > MAX_SCANNED_CONJUNCT_NODES {
                return None;
            }
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) {
                if name == "and" && !args.is_empty() {
                    let args = args.clone();
                    // Reverse push keeps the pop order left-to-right, so the
                    // first refutable conjunct in source order wins.
                    for (index, &child) in args.iter().enumerate().rev() {
                        let Ok(position) = u32::try_from(index) else {
                            return None;
                        };
                        let mut child_path = path.clone();
                        child_path.push(position);
                        stack.push((child, child_path));
                    }
                    continue;
                }
            }
            leaves.push((term, path));
        }
        Some(leaves)
    }

    /// How (if at all) `term` is refutable by evaluation alone.
    fn conjunct_eval_closer(
        &self,
        term: TermId,
        datatype_decls: &[(String, Vec<String>)],
        selector_decls: &[(String, Vec<String>)],
    ) -> Option<ConjunctEvalCloser> {
        if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) {
            if name == "=" && args.len() == 2 && args[0] == args[1] {
                return Some(ConjunctEvalCloser::Reflexivity);
            }
        }
        if !selector_decls.is_empty()
            && ay_proof::recognize_datatype_selector_project(
                &self.ctx.terms,
                &[term],
                selector_decls,
            )
        {
            return Some(ConjunctEvalCloser::Datatype(
                TheoryLemmaKind::DatatypeSelectorProject,
            ));
        }
        if !datatype_decls.is_empty()
            && ay_proof::recognize_datatype_tester_eval(&self.ctx.terms, &[term], datatype_decls)
        {
            return Some(ConjunctEvalCloser::Datatype(
                TheoryLemmaKind::DatatypeTesterEval,
            ));
        }
        // The remaining closers ask `ay-proof`'s OWN recognizers whether the
        // unit clause `(cl term)` is a theory tautology the strict validator
        // re-derives. Each recognizer is documented as the exact precondition
        // of its validator, so there is no classifier/checker drift: a `true`
        // here is a lemma `check_proof_strict_with_datatypes` accepts below,
        // and a `false` simply leaves the erasure as it was.
        //
        // ARRAY read-over-write chain evaluation. This is the shape a
        // preprocessor ROW fold leaves behind: `(assert (not (= (select
        // (store a 0 10) 0) 10)))` folds to the constant `false` because
        // `select(store(a,0,10),0)` evaluates to `10`, and that evaluation is
        // exactly sub-schema (A) of the `ArrayRowChain` validator. Before this
        // arm the fold's argument was unrecoverable and the document became
        // `(step t0 (cl) :rule hole)`, which mandatory certification then
        // declined by name — withdrawing a correct `unsat` to `unknown`.
        // `is_trust()` is re-checked because a recognizer must never route a
        // trust-family kind through a path advertised as trust-free.
        if let Some(kind) = ay_proof::recognize_array_theory_lemma(&self.ctx.terms, &[term]) {
            if !kind.is_trust() {
                return Some(ConjunctEvalCloser::TheoryLemma("arrays", kind));
            }
        }
        // GROUND string/regex evaluation, the QF_S counterpart of the same
        // fold: `(assert (= (str.++ "a" "b") "ac"))` is closed and false, and
        // the checker's independent Unicode-string evaluator decides it
        // outright.
        if ay_proof::recognize_string_ground_eval(&self.ctx.terms, &[term]) {
            return Some(ConjunctEvalCloser::TheoryLemma(
                "strings",
                TheoryLemmaKind::StringGroundEval,
            ));
        }
        None
    }
}
