// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared strict commit gate and authored-surface respelling.

use super::*;

impl Executor {
    /// Commit `candidate` over `proof` only when it derives the empty clause
    /// from authored assumptions AND the plain strict checker accepts it.
    ///
    /// This is the single fail-closed gate every reconstruction arm above ends
    /// at: a candidate the checker will not independently re-validate never
    /// replaces anything, so a mis-recognition costs completeness (the verdict
    /// stays `unknown`) and can never cost soundness.
    pub(in super::super) fn commit_if_strictly_checked(
        &mut self,
        proof: &mut Proof,
        candidate: Proof,
        authored: &[TermId],
    ) -> bool {
        if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, authored).is_ok()
            && Self::proof_derives_empty_clause(&candidate)
            && self
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete())
        {
            // Prefer the SAME reconstruction respelled over the problem file's
            // own terms, so an `assume` still matches the input syntactically.
            // The respelling is only accepted after re-running this very gate
            // on it; on any failure the canonical candidate is committed
            // exactly as before.
            let committed = self
                .respell_certified_proof_over_authored_surface(&candidate)
                .unwrap_or(candidate);
            self.purge_surface_overrides_for_certified_proof(&committed);
            *proof = committed;
            return true;
        }
        false
    }

    /// Rebuild an already-certified reconstruction over the RAW authored terms
    /// of the problem file, or `None` when that cannot be done.
    ///
    /// WHY. `purge_surface_overrides_for_certified_proof` makes the exported
    /// document internally consistent by printing every operand from the term
    /// the strict checker accepted. That is the identity rendering of the
    /// internal proof — but where elaboration FOLDED the source, the identity
    /// rendering is no longer the problem file's syntax, and Carcara matches
    /// `assume` against the original premises SYNTACTICALLY
    /// (`checker::shared::check_assume_shared`: exact hit, else `polyeq` mod
    /// reordering/n-ary — never mod `bvadd x #x00`). Measured on the
    /// `(bvadd p #x00)`-fold fixture, carcara 1.1.0 rejected the purged
    /// document with
    ///
    /// ```text
    /// [ERROR] checking failed on step 't0' with rule 'assume': could not match
    ///         term to any of the original problem premises:
    ///         (= mem2 (store mem p (_ bv16 8)))
    /// ```
    ///
    /// even though every derived step checked. The established precedent
    /// (`proof_trust_surgery.rs`, the array-ITE repair) keeps the authored ROOT
    /// spellings for exactly this reason. It cannot simply be copied here: a
    /// surface override re-spells ONE `TermId` EVERYWHERE, so keeping the root
    /// override would print the `eq_congruent` hypothesis
    /// `(= mem2 (store mem (bvadd p #x00) #x10))` beside a conclusion that
    /// reads `(select (store mem p #x10) p)` — the divergence the purge exists
    /// to remove, and one Carcara rejects at the congruence step instead. The
    /// two spellings are ONE interned term (`TermStore::mk_bvadd` folds
    /// `x + 0`), so no override assignment can print them apart, and no bridge
    /// step can relate them: `(= X X)` prints with one spelling on both sides.
    ///
    /// WHAT THIS DOES INSTEAD. It gives the two spellings two `TermId`s. Each
    /// assumed root is re-interned from its exact parse with
    /// `raw_intern_surface` — the same print-faithful constructor the
    /// self-contained surface path in `proof_original_rebuild.rs` already uses
    /// — and the canonical/raw pair is walked in lockstep to recover the
    /// position where elaboration folded (`p` <- `(bvadd p #x00)`). That map is
    /// applied to EVERY term of the certified candidate with raw constructors,
    /// so the whole reconstruction moves into the authored spelling at once:
    /// the store, the read, the reflexive congruence hypothesis and the ROW1
    /// index all carry the same authored index term, and each prints from its
    /// own `TermId` with no override in play.
    ///
    /// WHY THIS IS NOT THE INADMISSIBLE RESPELL. `bound_override_respells_target`
    /// refuses attaching `(bvadd p #x00)` to `p` as a PRINTING override,
    /// because printing is not re-checked: it silently renames the variable in
    /// every other assertion of the same document. Here nothing is renamed by
    /// fiat. The result is a DIFFERENT proof over different terms — a uniform
    /// substitution instance, which is sound for these schemas anyway — and it
    /// is put back through the whole gate: its assumes must land in the
    /// authored scope, it must still derive the empty clause, and
    /// `check_proof_strict_with_datatypes` must accept it from scratch. A
    /// respelling that renames a term another assume depends on produces an
    /// `assume` outside the authored scope and is refused right there.
    ///
    /// NO NEW AUTHORITY. The raw re-intern is admitted as an `assume` only when
    /// `last_proof_rebuild_originals` ALREADY holds it — the grant
    /// `rebuild_trust_leaf_proof_from_original_assertions` records for the raw
    /// re-intern of every parsed original, long before this pass runs. This
    /// function never calls `record_rebuilt_authored_proof_premise`, so it
    /// cannot widen the premise scope by even one term.
    ///
    /// That explicit test is a cheap early exit, NOT the authority itself:
    /// `check_proof_strict_with_datatypes` below independently re-derives the
    /// premise scope through `complete_problem_assertions_for_strict_proof`,
    /// which reads the same grant. Deleting the early test therefore still
    /// fails closed — measured: with the grant cleared, the respelling declines
    /// either way (`respelling_declines_a_raw_reintern_the_premise_scope_has_not_admitted`
    /// stays green under that mutation), because mandatory strict certification
    /// refuses an `assume` the problem never authorized.
    pub(super) fn respell_certified_proof_over_authored_surface(
        &mut self,
        candidate: &Proof,
    ) -> Option<Proof> {
        /// Work bound on the canonical/raw lockstep walk.
        const MAX_ALIGN_WORK: usize = 16 * 1024;
        /// Work bound on the term rewrite.
        const MAX_REWRITE_WORK: usize = 64 * 1024;

        // `Proof::from_steps` rebuilds the step DAG positionally but starts
        // with an empty name table, so a named `assume` would silently lose its
        // name. These reconstructions never name one; refuse rather than drop.
        if !candidate.named_steps.is_empty() {
            return None;
        }
        let originals = self.proof_original_problem_assertions();
        if originals.is_empty() || originals.len() != self.ctx.assertions_parsed().len() {
            return None;
        }

        let mut assumed: Vec<TermId> = Vec::new();
        for step in &candidate.steps {
            if let ProofStep::Assume(term) = step {
                if !assumed.contains(term) {
                    assumed.push(*term);
                }
            }
        }
        if assumed.is_empty() {
            return None;
        }
        // Only the assumed roots are re-interned, so a large assertion stack
        // costs nothing here.
        let mut sources: Vec<(TermId, FrontendTerm)> = Vec::with_capacity(assumed.len());
        for &root in &assumed {
            // Every assume of these reconstructions is an exact authored root;
            // anything else has no problem-file spelling to respell to.
            let index = originals.iter().position(|&original| original == root)?;
            sources.push((root, self.ctx.assertions_parsed().get(index)?.clone()));
        }

        let mut surface: ay_core::kani_compat::DetHashMap<TermId, TermId> =
            ay_core::kani_compat::DetHashMap::default();
        let mut raw_roots: Vec<TermId> = Vec::new();
        let mut align_work = MAX_ALIGN_WORK;
        for (root, source) in &sources {
            let root = *root;
            let raw = self.raw_intern_surface(source)?;
            if raw != root {
                // Authority is not created here — only reused. The raw
                // re-intern must already be an admitted authored premise.
                if !self.last_proof_rebuild_originals.contains(&raw) {
                    return None;
                }
                raw_roots.push(raw);
            }
            Self::align_authored_surface_spelling(
                &self.ctx.terms,
                root,
                raw,
                &mut surface,
                &mut align_work,
            )?;
        }
        // Nothing folded: the identity rendering already IS the problem file's
        // syntax up to constant notation, which Carcara reads as one term
        // (`#x10` and `#b00010000` both parse to `(_ bv16 8)`). The rewrite
        // below would be the identity and the gate would re-accept the same
        // proof, so this is an economy short-circuit, not a correctness guard —
        // it keeps a redundant strict replay off every commit.
        if raw_roots.is_empty() {
            return None;
        }

        let mut memo: ay_core::kani_compat::DetHashMap<TermId, TermId> =
            ay_core::kani_compat::DetHashMap::default();
        let mut rewrite_work = MAX_REWRITE_WORK;
        let respelled = self.respell_proof_steps_over_authored_surface(
            candidate,
            &surface,
            &mut memo,
            &mut rewrite_work,
        )?;

        let mut scope = self.exact_concrete_authored_scope();
        for &raw in &raw_roots {
            if !scope.contains(&raw) {
                scope.push(raw);
            }
        }
        if ay_proof::validate_reachable_assumes_in_problem_scope(&respelled, &scope).is_ok()
            && Self::proof_derives_empty_clause(&respelled)
            && self.check_proof_strict_with_datatypes(&respelled).is_ok()
        {
            Some(respelled)
        } else {
            None
        }
    }

    fn respell_proof_steps_over_authored_surface(
        &mut self,
        candidate: &Proof,
        surface: &ay_core::kani_compat::DetHashMap<TermId, TermId>,
        memo: &mut ay_core::kani_compat::DetHashMap<TermId, TermId>,
        rewrite_work: &mut usize,
    ) -> Option<Proof> {
        let mut steps: Vec<ProofStep> = Vec::with_capacity(candidate.steps.len());
        for step in &candidate.steps {
            let respelled = match step {
                ProofStep::Assume(term) => ProofStep::Assume(
                    self.respell_term_over_authored_surface(*term, surface, memo, rewrite_work, 0)?,
                ),
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => ProofStep::Resolution {
                    clause: self.respell_clause_over_authored_surface(
                        clause,
                        surface,
                        memo,
                        rewrite_work,
                    )?,
                    pivot: self.respell_term_over_authored_surface(
                        *pivot,
                        surface,
                        memo,
                        rewrite_work,
                        0,
                    )?,
                    clause1: *clause1,
                    clause2: *clause2,
                },
                ProofStep::TheoryLemma {
                    theory,
                    clause,
                    farkas,
                    kind,
                    lia,
                } => {
                    // Farkas / LIA annotations are positional over the clause
                    // this pass would rewrite; no reconstruction that reaches
                    // here carries one, so refuse rather than re-derive them.
                    if farkas.is_some() || lia.is_some() {
                        return None;
                    }
                    ProofStep::TheoryLemma {
                        theory: theory.clone(),
                        clause: self.respell_clause_over_authored_surface(
                            clause,
                            surface,
                            memo,
                            rewrite_work,
                        )?,
                        farkas: None,
                        kind: *kind,
                        lia: None,
                    }
                }
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => ProofStep::Step {
                    rule: rule.clone(),
                    clause: self.respell_clause_over_authored_surface(
                        clause,
                        surface,
                        memo,
                        rewrite_work,
                    )?,
                    premises: premises.clone(),
                    args: self.respell_clause_over_authored_surface(
                        args,
                        surface,
                        memo,
                        rewrite_work,
                    )?,
                },
                // Anchors bind variables whose scope this flat rewrite does not
                // model, and `ProofStep` is `#[non_exhaustive]`: refuse.
                _ => return None,
            };
            steps.push(respelled);
        }
        Some(Proof::from_steps(steps))
    }

    /// Walk a canonical root and its raw re-intern in lockstep, recording every
    /// node where the two differ.
    ///
    /// Alignment stops descending as soon as the two nodes are not the same
    /// application — that is exactly the position elaboration folded, and the
    /// pair recorded there is the whole content of the respelling. A node that
    /// would have to map to two different spellings, or whose sorts disagree,
    /// fails closed: a respelling is only ever a sort-preserving substitution.
    pub(super) fn align_authored_surface_spelling(
        terms: &TermStore,
        canonical: TermId,
        raw: TermId,
        surface: &mut ay_core::kani_compat::DetHashMap<TermId, TermId>,
        work: &mut usize,
    ) -> Option<()> {
        let mut stack = vec![(canonical, raw)];
        while let Some((canonical, raw)) = stack.pop() {
            if *work == 0 {
                return None;
            }
            *work -= 1;
            if canonical == raw {
                continue;
            }
            if terms.sort(canonical) != terms.sort(raw) {
                return None;
            }
            if *surface.entry(canonical).or_insert(raw) != raw {
                return None;
            }
            match (terms.get(canonical), terms.get(raw)) {
                (
                    TermData::App(canonical_sym, canonical_args),
                    TermData::App(raw_sym, raw_args),
                ) if canonical_sym == raw_sym && canonical_args.len() == raw_args.len() => {
                    stack.extend(canonical_args.iter().copied().zip(raw_args.iter().copied()));
                }
                (TermData::Not(canonical_inner), TermData::Not(raw_inner)) => {
                    stack.push((*canonical_inner, *raw_inner));
                }
                // The fold point: recorded above, nothing below it aligns.
                _ => {}
            }
        }
        Some(())
    }

    /// Respell every literal of one clause.
    fn respell_clause_over_authored_surface(
        &mut self,
        clause: &[TermId],
        surface: &ay_core::kani_compat::DetHashMap<TermId, TermId>,
        memo: &mut ay_core::kani_compat::DetHashMap<TermId, TermId>,
        work: &mut usize,
    ) -> Option<Vec<TermId>> {
        clause
            .iter()
            .map(|&literal| {
                self.respell_term_over_authored_surface(literal, surface, memo, work, 0)
            })
            .collect()
    }

    /// Rebuild `term` with every mapped subterm replaced by its authored
    /// spelling, using RAW constructors so the rebuild cannot re-fold what it
    /// just spelled out. A term with no mapped descendant is returned
    /// unchanged, so nothing outside the authored surface is disturbed.
    fn respell_term_over_authored_surface(
        &mut self,
        term: TermId,
        surface: &ay_core::kani_compat::DetHashMap<TermId, TermId>,
        memo: &mut ay_core::kani_compat::DetHashMap<TermId, TermId>,
        work: &mut usize,
        depth: u32,
    ) -> Option<TermId> {
        /// Native stack guard; `work` is the real terminator.
        const MAX_DEPTH: u32 = 512;

        if let Some(&mapped) = surface.get(&term) {
            return Some(mapped);
        }
        if let Some(&cached) = memo.get(&term) {
            return Some(cached);
        }
        if *work == 0 || depth > MAX_DEPTH {
            return None;
        }
        *work -= 1;

        let respelled = match self.ctx.terms.get(term).clone() {
            TermData::Const(_) | TermData::Var(..) => term,
            TermData::App(symbol, args) => {
                let mut respelled_args = Vec::with_capacity(args.len());
                let mut changed = false;
                for argument in args {
                    let respelled_argument = self.respell_term_over_authored_surface(
                        argument,
                        surface,
                        memo,
                        work,
                        depth + 1,
                    )?;
                    changed |= respelled_argument != argument;
                    respelled_args.push(respelled_argument);
                }
                if changed {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(symbol, respelled_args, sort)
                } else {
                    term
                }
            }
            TermData::Not(inner) => {
                let respelled_inner =
                    self.respell_term_over_authored_surface(inner, surface, memo, work, depth + 1)?;
                if respelled_inner == inner {
                    term
                } else {
                    self.ctx.terms.mk_not_raw(respelled_inner)
                }
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                let mut respelled = [condition, then_branch, else_branch];
                for slot in &mut respelled {
                    *slot = self.respell_term_over_authored_surface(
                        *slot,
                        surface,
                        memo,
                        work,
                        depth + 1,
                    )?;
                }
                if respelled == [condition, then_branch, else_branch] {
                    term
                } else {
                    self.ctx
                        .terms
                        .mk_ite_raw(respelled[0], respelled[1], respelled[2])
                }
            }
            // Binders and lets: a respelling under a binder would have to model
            // shadowing. Keep such a term only when nothing below it moved.
            _ => {
                for child in self.ctx.terms.children(term) {
                    if self.respell_term_over_authored_surface(
                        child,
                        surface,
                        memo,
                        work,
                        depth + 1,
                    )? != child
                    {
                        return None;
                    }
                }
                term
            }
        };
        memo.insert(term, respelled);
        Some(respelled)
    }
}
