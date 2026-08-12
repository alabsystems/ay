// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared support for authored congruence reconstruction and commit.

use super::*;

/// How one argument position's premise literal is discharged.
enum Discharge {
    /// The exact authored equality root proving this position.
    Authored(TermId),
    /// Both sides are the same term: `(= a a)` by `eq_reflexive`.
    Reflexive,
}

impl Executor {
    /// Whether `application` applies a symbol the problem DECLARED as a
    /// datatype constructor.
    ///
    /// Re-derived from `datatype_decls_for_strict_proof` — the same declaration
    /// snapshot the strict checker hands to `ay_proof::recognize_datatype_distinct`
    /// — so the answer follows the problem's `declare-datatypes`, never a name
    /// pattern, a spelling, or a capitalization convention. A problem with no
    /// datatype declarations has an empty snapshot and every application answers
    /// `false`.
    ///
    /// This decides OWNERSHIP between two reconstruction passes, never the
    /// validity of a step: both possible answers leave the emitted proof subject
    /// to the same unchanged `check_proof_strict_with_datatypes` gate.
    pub(super) fn applies_declared_datatype_constructor(
        terms: &TermStore,
        datatype_decls: &[(String, Vec<String>)],
        application: TermId,
    ) -> bool {
        let TermData::App(symbol, arguments) = terms.get(application) else {
            return false;
        };
        if arguments.is_empty() {
            return false;
        }
        let name = symbol.name();
        datatype_decls
            .iter()
            .any(|(_, constructors)| constructors.iter().any(|c| c == name))
    }

    /// Derive the unit clause `(cl (= lhs rhs))` by CONGRUENCE inside
    /// `candidate`, drawing every argument premise from the exact authored
    /// scope, and return the step proving it together with the equality term.
    ///
    /// Declines (leaving `candidate` untouched apart from unreferenced steps)
    /// when the two terms are not applications of one symbol at one arity, or
    /// when some argument position has no exact authored equality. An argument
    /// position whose two sides are the SAME term is discharged by
    /// [`TheoryLemmaKind::EufReflexive`] rather than by a premise no one
    /// authored.
    ///
    /// Nothing here is trusted: the emitted clause is re-decided by the strict
    /// `EufCongruent` validator, which requires exactly one negated-equality
    /// premise per argument position, each connecting that position's two
    /// arguments.
    pub(in super::super) fn derive_authored_congruence_unit(
        &mut self,
        candidate: &mut Proof,
        lhs: TermId,
        rhs: TermId,
        authored_equalities: &[(TermId, TermId, TermId)],
    ) -> Option<(ProofId, TermId)> {
        /// Work bound. Each candidate costs O(arity) authored-scope scans and
        /// one strict replay. Declining an oversized application leaves the
        /// verdict exactly as it is today.
        const MAX_CONGRUENCE_ARITY: usize = 16;

        let (f_symbol, f_args) = as_app_local(&self.ctx.terms, lhs)?;
        let (g_symbol, g_args) = as_app_local(&self.ctx.terms, rhs)?;
        // Cheap necessary conditions of the schema — the checker's validator
        // re-decides all of them on the clause it is handed.
        if f_symbol != g_symbol
            || f_args.len() != g_args.len()
            || f_args.is_empty()
            || f_args.len() > MAX_CONGRUENCE_ARITY
        {
            return None;
        }

        let premises = self.authored_congruence_premises(&f_args, &g_args, authored_equalities)?;
        let congruence_equality = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
        // (cl (not (= a_1 b_1)) .. (not (= a_n b_n)) (= (f a) (f b)))
        let mut clause: Vec<TermId> = premises
            .iter()
            .map(|(equality, _)| self.ctx.terms.mk_not_raw(*equality))
            .collect();
        clause.push(congruence_equality);

        let mut current = candidate.add_theory_lemma_with_kind(
            "euf",
            clause.clone(),
            TheoryLemmaKind::EufCongruent,
        );
        let mut remaining = clause;
        for (equality, discharge) in &premises {
            let negated = self.ctx.terms.mk_not_raw(*equality);
            // Resolution removes ONE occurrence; a repeated argument pair would
            // otherwise leave a literal behind and the residual check below
            // rejects the candidate.
            let position = remaining.iter().position(|&literal| literal == negated)?;
            let _ = remaining.remove(position);
            let support = match discharge {
                Discharge::Authored(root) => candidate.add_assume(*root, None),
                Discharge::Reflexive => candidate.add_theory_lemma_with_kind(
                    "euf",
                    vec![*equality],
                    TheoryLemmaKind::EufReflexive,
                ),
            };
            current = candidate.add_resolution(remaining.clone(), *equality, current, support);
        }
        if remaining != vec![congruence_equality] {
            return None;
        }
        Some((current, congruence_equality))
    }

    fn authored_congruence_premises(
        &mut self,
        f_args: &[TermId],
        g_args: &[TermId],
        authored_equalities: &[(TermId, TermId, TermId)],
    ) -> Option<Vec<(TermId, Discharge)>> {
        let mut premises: Vec<(TermId, Discharge)> = Vec::with_capacity(f_args.len());
        for (&left_arg, &right_arg) in f_args.iter().zip(g_args.iter()) {
            if left_arg == right_arg {
                let equality =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("="), [left_arg, right_arg], Sort::Bool);
                premises.push((equality, Discharge::Reflexive));
                continue;
            }
            // The premise must be an EXACT authored root, in the authored
            // orientation. The validator accepts either orientation, so no
            // normalization happens here.
            let &(root, _, _) = authored_equalities.iter().find(|&&(_, a, b)| {
                (a == left_arg && b == right_arg) || (a == right_arg && b == left_arg)
            })?;
            premises.push((root, Discharge::Authored(root)));
        }
        Some(premises)
    }

    /// Override-purge discipline for a committed authored reconstruction:
    /// drop every stale surface spelling attached to a term this proof PRINTS,
    /// so one internal term cannot reach the printer under two spellings.
    ///
    /// Mirrors the same discipline the trichotomy / assume-bridge surgery
    /// already applies (`proof_trust_surgery.rs`). These reconstructions build
    /// every non-`assume` step out of freshly interned canonical terms, while
    /// the ordinary export collected the problem file's spellings for the
    /// authored roots and their subterms. Those two renderings of one `TermId`
    /// collide inside a single certified step whenever elaboration FOLDED the
    /// source — an authored `(bvadd p #x00)` hash-conses to `p`, an authored
    /// `#x01` is the interned constant whose canonical rendering is
    /// `#b00000001` — so the printed `eq_congruent` hypothesis `(= p p)` sits
    /// next to the operand `(bvadd p #x00)`, and the printed ROW1 store value
    /// `#xAA` next to the separately printed `#b10101010`. The printer's
    /// surface validators are RIGHT to refuse those steps: as printed they do
    /// not correspond to the step the checker validated.
    ///
    /// Purging cannot hide such a divergence, because after it there is none:
    /// every operand of every certified step is rendered from the very term
    /// the strict checker just accepted, which is the identity rendering of
    /// the internal proof. It removes information (the problem file's
    /// spelling), never adds authority — and it cannot re-spell a term as
    /// something else, which is precisely what registering the enclosing
    /// spelling on a folded operand would do (see
    /// `bound_override_respells_target`: attaching `(bvadd p #x00)` to `p`
    /// renames the variable everywhere instead of re-spelling the sum).
    ///
    /// Scoped to the terms this candidate prints; unrelated entries survive
    /// for whatever the later export passes still render.
    pub(super) fn purge_surface_overrides_for_certified_proof(&mut self, candidate: &Proof) {
        /// Work bound on the printed-term closure. An oversized reconstruction
        /// keeps today's spellings and simply stays unexportable.
        const MAX_PRINTED_TERMS: usize = 64 * 1024;

        let Some(mut overrides) = self.last_proof_term_overrides.clone() else {
            return;
        };

        let mut printed: ay_core::kani_compat::DetHashSet<TermId> =
            ay_core::kani_compat::DetHashSet::default();
        let mut stack: Vec<TermId> = Vec::new();
        for step in &candidate.steps {
            match step {
                ProofStep::Assume(term) => stack.push(*term),
                ProofStep::Resolution { clause, pivot, .. } => {
                    stack.extend(clause.iter().copied());
                    stack.push(*pivot);
                }
                ProofStep::TheoryLemma { clause, .. } => stack.extend(clause.iter().copied()),
                ProofStep::Step { clause, args, .. } => {
                    stack.extend(clause.iter().copied());
                    stack.extend(args.iter().copied());
                }
                ProofStep::Anchor { .. } => {}
                // `ProofStep` is `#[non_exhaustive]`. A kind whose terms this
                // walk does not know how to enumerate could leave a stale
                // spelling behind on a term the document prints, so purge
                // NOTHING and keep exactly today's behaviour: the printer then
                // declines the divergence as it does now.
                _ => return,
            }
        }
        while let Some(term) = stack.pop() {
            if printed.len() >= MAX_PRINTED_TERMS {
                return;
            }
            if !printed.insert(term) {
                continue;
            }
            stack.extend(self.ctx.terms.children(term));
        }

        for term in &printed {
            overrides.remove(term);
        }
        self.last_proof_term_overrides = Some(overrides);
    }
}
