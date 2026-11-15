// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Record the argument behind a preprocessor fold-to-`false` whose cause is a
//! SHARED quantifier.
//!
//! ## The class, as measured
//!
//! Alpha-quantifier sharing (`elaborate/term.rs::share_alpha_equivalent_quantifier`)
//! makes two syntactically identical authored quantifiers elaborate to ONE
//! term. On the AUFDTLIA `fmf-cav2013 agreement` family the authored goal is
//! the negation of a propositional tautology whose atoms include such a
//! quantifier — `agree202`, with the guards elided:
//!
//! ```text
//! (assert (not (=> (and (and (=> (> round (+ t 1)) Q) B) C)
//!                  (=> g1 (=> g2 (=> g3 (=> g4 (=> g5
//!                      (=> (> round (+ t 1)) Q)))))))))
//! ```
//!
//! where `Q = (forall ((n node$type)) (= (select chosen n) Truth))` is written
//! twice. Once both occurrences are the same term, `A = (=> (> round (+ t 1))
//! Q)` is literally a conjunct of the hypothesis AND literally the innermost
//! consequent. Elaboration then folds the root away without recording it:
//! `mk_implies` is `mk_or([mk_not(lhs), rhs])`, the outer `mk_not` pushes De
//! Morgan back to `mk_and([H, (not G)])`, flattening lifts `A` out of `H` and
//! `(not A)` out of `(not G)` into one argument list, and `mk_and`'s
//! complement scan (`ay-core/src/term/boolean.rs`) returns the constant
//! `false`. No `TermId` for the authored root is ever created.
//!
//! Everything downstream then sees a proof whose only leaf is `assume false`,
//! and `false_source::demote_unattributed_assumed_false` erases it to
//! `(step t0 (cl) :rule hole)`. Measured on `agree202` at `ec898d4575`: the
//! verdict is `unsat` under `--no-proof`, `--rigor fast`, `--competition` and
//! `--z3-mode`, and `unknown` under the default `--rigor standard` and under
//! `--rigor certified` — a refutation AY has and throws away for want of an
//! argument.
//!
//! ## Why the argument is recoverable, and what it is NOT
//!
//! It is not a re-elaboration. A predecessor branch tried re-elaborating the
//! folded root with sharing OFF and measuring it: on the full 497-file family
//! that gamble fired on 142 files, recovered 29, and cost 24x the wall time on
//! the 113 it did not recover. Nothing here re-runs the solver, and nothing
//! here consults a posture. The fold's own argument is already complete, and
//! purely propositional:
//!
//! ```text
//! (assume h0 (not (=> H G)))
//! (step t1 (cl H)       :rule not_implies1 :premises (h0))
//! (step t2 (cl (not G)) :rule not_implies2 :premises (h0))
//!   ... one not_implies2 per implication peeled off the consequent chain,
//!       ending in (cl (not A))
//!   ... one and_pos + resolution per level of the hypothesis and-tree,
//!       ending in (cl A)
//! (step tn (cl) :rule resolution :premises (...))
//! ```
//!
//! `A` is the SAME `TermId` on both sides — that shared identity is the entire
//! content of the refutation, and the resolution step DISCHARGES it rather
//! than asserting it. Every rule is a standard Alethe rule that AY's strict
//! checker re-derives structurally (`validate_not_implies1`,
//! `validate_not_implies2`, `validate_and_pos`) and that the pinned external
//! checker also carries.
//!
//! ## What keeps this honest
//!
//! 1. The single `assume` is the author's own assertion, re-interned RAW from
//!    the parsed surface so the folding constructors cannot touch it, and then
//!    rendered through the exporter's own printer and re-parsed until it is
//!    the author's parsed assertion again (`rebuilt_root_prints_as_authored`).
//!    A premise that cannot be matched to a problem assertion is the one
//!    outcome strictly worse than the hole this replaces.
//! 2. The quantifier inside it is never rebuilt. It is the term elaboration
//!    already interned, so this pass cannot manufacture the sharing it relies
//!    on: if the two authored quantifiers are not the same term, no conjunct
//!    of `H` matches any tail consequent of `G`, the search finds nothing, and
//!    the erasure proceeds untouched.
//! 3. Nothing is taken on the producer's word. The UNCHANGED strict checker
//!    must accept the whole candidate as COMPLETE, and the exporter's own
//!    authority check must accept its `assume` against the exporter's own
//!    premise set, before anything is committed.

use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermId};
use ay_frontend::command::Term as FrontendTerm;

use super::Executor;

/// Upper bound on implications peeled off one consequent chain. The measured
/// family depth is 1-8; this only stops a pathological root.
const MAX_CONSEQUENT_CHAIN: usize = 512;

/// Upper bound on hypothesis `and`-tree nodes inspected per authored root.
/// The same second, independent stop `authored_conjunct_eval` applies, so a
/// pathological tree cannot turn a bounded root into an unbounded search.
const MAX_SCANNED_CONJUNCT_NODES: usize = 8_192;

impl Executor {
    /// Replace a proof that rests on an unattributed `assume false` with the
    /// propositional derivation the fold actually had. `true` when a
    /// strictly-checked, export-authorized replacement was committed.
    pub(super) fn replace_with_exact_authored_shared_tautology_refutation(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        // Charged against the SAME query-local envelope every other
        // source-touching pass shares, so this pass cannot spend work the
        // aggregate ceiling has not authorized.
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
        for assertion in &parsed {
            if self.try_authored_shared_tautology_refutation(proof, assertion) {
                return true;
            }
        }
        false
    }

    fn try_authored_shared_tautology_refutation(
        &mut self,
        proof: &mut Proof,
        assertion: &FrontendTerm,
    ) -> bool {
        let mut quantifiers: Vec<(TermId, FrontendTerm)> = Vec::new();
        let Some(root) = self.raw_intern_surface_sharing_quantifiers(assertion, &mut quantifiers)
        else {
            return false;
        };
        if !matches!(self.ctx.terms.sort(root), Sort::Bool) {
            return false;
        }
        // Elaboration alpha-renames bound variables, so the rebuilt root
        // renders `(forall ((n_2 Int)) (f n_2))` where the author wrote
        // `((n Int))`. The structure is already exact — only the binder's
        // NAME differs — but an `assume` spelled that way is one no external
        // checker can match to a problem premise, which is the single worst
        // outcome on this path. Register the authored spelling for each binder
        // leaf through the exporter's own collector — transactionally. Every
        // ledger this pass touches is snapshotted here and restored on EVERY
        // decline, so a pass that does not commit leaves the executor
        // byte-identical to how it found it.
        let saved_overrides = self.last_proof_term_overrides.clone();
        let saved_premises = self.last_proof_rebuild_originals.clone();
        let saved_raw_originals = self.last_proof_raw_original_assertions.clone();
        let restore = |executor: &mut Self| {
            executor.last_proof_term_overrides = saved_overrides.clone();
            executor.last_proof_rebuild_originals = saved_premises.clone();
            executor.last_proof_raw_original_assertions = saved_raw_originals.clone();
        };
        if !self.install_authored_quantifier_spellings(&quantifiers) {
            restore(self);
            return false;
        }
        // PREMISE AUTHENTICITY, and it runs before any step is built: render
        // the rebuilt root through the exporter's own printer, re-parse it,
        // and demand the author's own parsed assertion back. A root that fails
        // this can never become an `assume`, whatever derivation would stand
        // on it.
        if !self.rebuilt_root_prints_as_authored(root, assertion) {
            restore(self);
            return false;
        }
        // Only now is `root` known to BE the author's assertion, re-interned
        // raw from its parsed surface, so record it as one. Both ledgers are
        // needed and they answer different gates:
        //
        // * proof authority, or the strict checker answers
        //   `UnauthorizedAssumption` — `ctx.assertions` holds the folded
        //   `false` and nothing else remembers the root;
        // * exact raw problem provenance, or the Alethe printer's
        //   `resolve_reachable_authored_sources` refuses the `assume` as
        //   unauthenticated and declines the whole document
        //   (`authored-source-authority-invalid`), which is how this pass
        //   first presented: a strictly-checked refutation with no renderable
        //   authored-scope form.
        //
        // `record_raw_authored_problem_assertion` mints both, and its stated
        // precondition — "matched the term against a PARSED assertion of the
        // problem" — is what the round-trip immediately above establishes.
        self.record_raw_authored_problem_assertion(root);
        let Some(candidate) = self.shared_tautology_candidate(root) else {
            restore(self);
            return false;
        };
        // DERIVATION. The UNCHANGED strict checker is the only authority that
        // commits this: it re-derives every `not_implies1`, `not_implies2` and
        // `and_pos` structurally and re-runs the resolutions.
        if !Self::proof_derives_empty_clause(&candidate)
            || !self
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete())
        {
            restore(self);
            return false;
        }
        // EXPORT AUTHORITY. The strict checker's premise set is a strict
        // superset of the exporter's, so a document it accepts can still be
        // refused at export — the one outcome strictly worse than the hole
        // this replaces. Ask the exporter's own check against the exporter's
        // own set before committing anything.
        if ay_proof::validate_reachable_assumes_in_problem_scope(
            &candidate,
            &self.proof_export_scope_assertions(),
        )
        .is_err()
        {
            restore(self);
            return false;
        }
        // RENDER. The gate above decides whether the `assume` is in scope; it
        // never asks whether the document can be PRINTED, and those are
        // different questions. A candidate every other gate accepts can still
        // be refused by the printer, and that refusal is not a quiet
        // downgrade: under `--proof FILE` it is a hard `#8821` failure that
        // publishes NO verdict and exits 1, and in the default posture it
        // drops the artifact entirely — strictly worse than the hole this
        // pass exists to replace. So run the EXPORTER ITSELF, with the
        // arguments `try_export_last_proof_alethe_for_problem_scope` uses, and
        // decline on anything it will not print.
        //
        // The budget is the bounded one on purpose: a document that renders
        // within it renders on the uncapped `--proof`/`--strict-proofs` paths
        // too, since a budget only ever adds a refusal.
        if !self.shared_tautology_candidate_renders(&candidate) {
            restore(self);
            return false;
        }
        *proof = candidate;
        true
    }

    /// Does the EXPORTER accept this candidate? Same call, same scope, same
    /// overrides and authored shells the CLI's own Alethe export makes.
    ///
    /// This is the invariant the pass rests on — never leave the query worse
    /// off than the bare hole — and it is the only gate that can see a printer
    /// refusal. The arity guard in `shared_tautology_conjuncts` removes the
    /// one shape measured to reach it; this removes the CLASS, so a later
    /// widening of the search cannot reopen the hard-failure path.
    fn shared_tautology_candidate_renders(&self, candidate: &Proof) -> bool {
        let Some(scope) = self.proof_export_scope_assertions_for(candidate) else {
            return false;
        };
        let overrides = self.proof_export_term_overrides();
        let shells = self.authored_negation_shell_spellings().bridgeable;
        self.in_alethe_dialect(|| {
            ay_proof::try_export_alethe_with_authored_assume_shells(
                candidate,
                &self.ctx.terms,
                &scope,
                overrides.as_ref(),
                (!shells.is_empty()).then_some(&shells),
                Some(super::DEFAULT_ALETHE_EMISSION_WORK_BUDGET),
            )
        })
        .is_ok()
    }

    /// Register each binder leaf's AUTHORED spelling with the printer, through
    /// `collect_surface_term_overrides` — the exporter's own collector, which
    /// re-elaborates each surface subterm under the binder it recovered from
    /// the already-elaborated quantifier and attaches it only to its own
    /// hash-consed term. `false` leaves the caller to restore the map.
    ///
    /// This grants no authority. An override changes how a term PRINTS, never
    /// what it is or what may be assumed; the premise round-trip immediately
    /// after re-parses the result and demands the author's own parsed
    /// assertion back, so a wrong spelling fails closed there.
    fn install_authored_quantifier_spellings(
        &mut self,
        quantifiers: &[(TermId, FrontendTerm)],
    ) -> bool {
        if quantifiers.is_empty() {
            // Nothing to spell. A root with no binder is not this class — the
            // binder-free promoters already own it — so decline rather than
            // race them for it.
            return false;
        }
        if !crate::executor::proof_surface_syntax::surface_override_roots_have_bounded_work(
            &self.ctx.terms,
            quantifiers.iter().map(|&(term, _)| term),
        ) {
            return false;
        }
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        if !crate::executor::proof_surface_syntax::surface_override_map_is_bounded(&overrides) {
            return false;
        }
        for (term, parsed) in quantifiers {
            if !crate::executor::proof_surface_syntax::collect_surface_term_overrides(
                &mut self.ctx,
                *term,
                parsed,
                &mut overrides,
            ) || !crate::executor::proof_surface_syntax::surface_override_map_is_bounded(
                &overrides,
            ) {
                return false;
            }
        }
        self.last_proof_term_overrides = Some(overrides);
        true
    }

    /// The fold's own refutation of one authored root, or `None` when this
    /// root is not of the class.
    fn shared_tautology_candidate(&mut self, root: TermId) -> Option<Proof> {
        let TermData::Not(tautology) = self.ctx.terms.get(root) else {
            return None;
        };
        let tautology = *tautology;
        let (hypothesis, consequent) = self.binary_implication(tautology)?;

        // Every formula the consequent chain refutes, outermost first:
        // `(not G)` is immediate, and `(not (=> p q))` yields `(not q)`.
        let mut refuted: Vec<TermId> = vec![consequent];
        let mut current = consequent;
        while refuted.len() < MAX_CONSEQUENT_CHAIN {
            let Some((_, inner)) = self.binary_implication(current) else {
                break;
            };
            if refuted.contains(&inner) {
                break;
            }
            refuted.push(inner);
            current = inner;
        }

        // Every formula the hypothesis proves, with the child-index path that
        // reaches it.
        let conjuncts = self.shared_tautology_conjuncts(hypothesis)?;

        // The refutation exists exactly where those two sets meet, and the
        // shallowest meeting point is the shortest document.
        let (target, path, depth) = refuted.iter().enumerate().find_map(|(depth, &term)| {
            conjuncts
                .iter()
                .find(|(conjunct, _)| *conjunct == term)
                .map(|(_, path)| (term, path.clone(), depth))
        })?;

        let mut candidate = Proof::new();
        let assume = candidate.add_assume(root, None);
        let hypothesis_step = candidate.add_rule_step(
            AletheRule::NotImplies1,
            vec![hypothesis],
            vec![assume],
            Vec::new(),
        );
        let positive = Self::emit_and_pos_chain(
            &mut self.ctx.terms,
            &mut candidate,
            hypothesis_step,
            hypothesis,
            &path,
            target,
        )?;

        // One `not_implies2` per level, from the root's own negation down to
        // `(cl (not target))`.
        let mut negative = assume;
        let mut current = tautology;
        for _ in 0..=depth {
            let (_, inner) = self.binary_implication(current)?;
            let negated = self.ctx.terms.mk_not_raw(inner);
            // A folded negation would make the clause say something other than
            // what the rule derives, so require the explicit outer `not`.
            if !matches!(self.ctx.terms.get(negated), TermData::Not(held) if *held == inner) {
                return None;
            }
            negative = candidate.add_rule_step(
                AletheRule::NotImplies2,
                vec![negated],
                vec![negative],
                Vec::new(),
            );
            current = inner;
        }
        if current != target {
            return None;
        }
        // `add_resolution` wants the premise carrying the pivot's NEGATIVE
        // occurrence first.
        candidate.add_resolution(Vec::new(), target, negative, positive);
        Some(candidate)
    }

    /// The two sides of a BINARY `(=> a b)`. An n-ary `=>` is refused: Alethe's
    /// `not_implies1`/`not_implies2` are binary, so a wider application has no
    /// step this pass may emit.
    fn binary_implication(&self, term: TermId) -> Option<(TermId, TermId)> {
        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    }

    /// Every node of the raw `and`-tree rooted at `root` — interior nodes and
    /// leaves alike, the root itself included — paired with the child-index
    /// path that reaches it. `None` when the tree is larger than the bound.
    fn shared_tautology_conjuncts(&self, root: TermId) -> Option<Vec<(TermId, Vec<u32>)>> {
        let mut nodes: Vec<(TermId, Vec<u32>)> = Vec::new();
        let mut stack: Vec<(TermId, Vec<u32>)> = vec![(root, Vec::new())];
        let mut visited = 0usize;
        while let Some((term, path)) = stack.pop() {
            visited += 1;
            if visited > MAX_SCANNED_CONJUNCT_NODES {
                return None;
            }
            nodes.push((term, path.clone()));
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) {
                // A UNIT `(and X)` is a leaf here, never a projection source.
                // Alethe's `and_pos` names one conjunct of a FLAT conjunction,
                // and the printer enforces that literally
                // (`alethe_printer/surface_and_pos.rs`: "and_pos source is not
                // a flat Boolean and-term" below arity 2). AY's strict checker
                // and the export-scope check both accept the 1-ary step, so
                // descending here produced a candidate that passed every gate
                // and was then refused by the RENDER — `--proof FILE` exited 1
                // with no verdict at all, and the default posture emitted no
                // artifact where the base still wrote its holey one. Treating
                // the unit `and` as opaque simply loses the projection: the
                // search finds no target and the erasure proceeds, which is
                // the outcome this pass promises whenever it cannot do better.
                if name == "and" && args.len() >= 2 {
                    let args = args.clone();
                    // Reverse push keeps the pop order left-to-right, so the
                    // first matching conjunct in source order wins.
                    for (index, &child) in args.iter().enumerate().rev() {
                        let position = u32::try_from(index).ok()?;
                        let mut child_path = path.clone();
                        child_path.push(position);
                        stack.push((child, child_path));
                    }
                }
            }
        }
        Some(nodes)
    }
}

#[cfg(test)]
#[path = "authored_shared_tautology_tests.rs"]
mod tests;
