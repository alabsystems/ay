// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared support for authored congruence reconstruction and commit.

use super::*;
use crate::executor::{proof_surface_syntax, NATIVE_API_ASSERTION_PLACEHOLDER};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

#[path = "authored_congruence_support/source_resolution.rs"]
mod source_resolution;
use source_resolution::{AuthoredSourceResolutionFailure, ReachableAuthoredSource};

const MAX_REACHABLE_AUTHORED_ASSUMES: usize = 8_192;
// `pub(super)` only so the sibling regression module can pin the cap by name
// instead of restating its value.
pub(super) const MAX_AUTHORED_ORIGINAL_INDEX_ROWS: usize = 100_000;
const MAX_AUTHORED_REACHABILITY_STEPS: usize = 1_000_000;
const MAX_REBUILD_AUTHORITY_ROWS: usize = 300_000;

/// How one argument position's premise literal is discharged.
enum Discharge {
    /// The exact authored equality root proving this position.
    Authored(TermId),
    /// Both sides are the same term: `(= a a)` by `eq_reflexive`.
    Reflexive,
}

/// Walk backward from every empty-clause derivation and collect the unique
/// assumptions that can affect publication. `ProofStep` is non-exhaustive
/// across this crate boundary, so an unknown dependency shape declines the
/// entire plan instead of being guessed premise-free.
fn reachable_authored_assume_roots(proof: &Proof) -> Option<Vec<TermId>> {
    if proof.steps.len() > MAX_AUTHORED_REACHABILITY_STEPS {
        return None;
    }
    let mut reachable = vec![false; proof.steps.len()];
    let mut stack = Vec::new();
    for (index, step) in proof.steps.iter().enumerate() {
        let derives_empty = match step {
            ProofStep::Step { clause, .. }
            | ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. } => clause.is_empty(),
            ProofStep::Assume(_) | ProofStep::Anchor { .. } => false,
            _ => return None,
        };
        if derives_empty {
            reachable[index] = true;
            stack.push(index);
        }
    }
    while let Some(index) = stack.pop() {
        let mut push = |premise: ProofId| {
            let premise = premise.0 as usize;
            let Some(reachable) = reachable.get_mut(premise) else {
                return false;
            };
            if !*reachable {
                *reachable = true;
                stack.push(premise);
            }
            true
        };
        match &proof.steps[index] {
            ProofStep::Step { premises, .. } => {
                for &premise in premises {
                    if !push(premise) {
                        return None;
                    }
                }
            }
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                if !push(*clause1) || !push(*clause2) {
                    return None;
                }
            }
            ProofStep::Anchor { end_step, .. } => {
                if !push(*end_step) {
                    return None;
                }
            }
            ProofStep::Assume(_) | ProofStep::TheoryLemma { .. } => {}
            _ => return None,
        }
    }

    let mut roots = Vec::new();
    let mut seen = DetHashSet::default();
    for (index, step) in proof.steps.iter().enumerate() {
        if !reachable[index] {
            continue;
        }
        if let ProofStep::Assume(root) = step {
            if seen.insert(*root) {
                if roots.len() >= MAX_REACHABLE_AUTHORED_ASSUMES {
                    return None;
                }
                roots.push(*root);
            }
        }
    }
    Some(roots)
}

/// Whether restoring `source` as the printed spelling of `root` keeps the
/// literal's top-level Boolean shape, so the Alethe printer's authored-assume
/// channel can confine it to its own `assume` step.
///
/// A surface override re-spells ONE `TermId` for the WHOLE document
/// (`proof_export_term_overrides` hands `last_proof_term_overrides` to the
/// printer as `term_overrides`). The printer removes that hazard by proving
/// `source = canonical` with stock rules and resolving the `assume` back to
/// the canonical unit -- but only for the spellings it can actually derive:
/// a comparison reversal (`comp_simplify`), a numeric multiplication reorder
/// (`aci_simp`), or `cong` UNDER THE CANONICAL ROOT'S OWN OPERATOR
/// (`alethe_printer/authored_assume/equivalence.rs` splits the surface text
/// with `split_application(surface, canonical_operator)` and gives up when
/// that fails). A source whose top-level connective is not the canonical
/// root's reaches none of those arms: the printer records it `unsupported`,
/// the entry stays document-wide, and it re-spells every other printed
/// occurrence of the same term.
///
/// Measured shape, `qfax_store_permutation_*`: `(assert (! (distinct i j)
/// :named neq))` elaborates to `(not (= i j))`. Restoring `(distinct i j)` on
/// that root prints the assume literal as an opaque `distinct` atom while the
/// resolution's other premise still prints `(= i j)`, and the printer's own
/// pre-existing guard `surface_resolution_needs_distinct_bridge` correctly
/// refuses the document with "a printed distinct/equality pivot cannot be
/// bridged to the authored operands". Withholding restores nothing and
/// removes nothing: the root keeps the canonical spelling the strict checker
/// validated, exactly the state
/// `purge_surface_overrides_for_certified_proof` established.
///
/// This is a NARROWING of a presentation-only pass, never a relaxation of an
/// authority check: an unconfinable root is still required to have exactly one
/// immutable authored source row before it gets here.
fn authored_surface_is_assume_confinable(
    terms: &TermStore,
    root: TermId,
    source: &FrontendTerm,
) -> bool {
    let canonical_operator = match terms.get(root) {
        TermData::Not(_) => "not",
        TermData::App(symbol, _) => symbol.name(),
        // A variable / constant / ite / binder root has no top-level operator
        // an override could rewrite, so there is nothing to compare and the
        // decision stays where it already lives: `override_would_hijack_atom`
        // refuses whole-assertion spellings on an ATOMIC canonical, exempting
        // exactly the VARIABLE fold result
        // (`authored_conjunction_folded_onto_variable`), which the printer then
        // confines with `plan_folded_and_assumes`.
        //
        // That exemption is about ATOMS ONLY, and this arm inherits no more
        // than it. A COMPOSITE fold result -- `(and (not p) (= x x))` interns
        // as `(not p)`, `(and (= a b) (= x x))` as `(= a b)` -- is a `Not`/`App`
        // root, so it reaches the head comparison below and is WITHHELD
        // wherever the authored head differs, which is where this pass used to
        // install. Measured on both, at `dacc7939c7` and here:
        //
        // * `(assert (and (not p) (= x x)))` + `(assert p)`: the earlier
        //   `proof_original_rebuild` collection already holds the authored
        //   conjunction on the folded root, `Untouched` removes nothing, and
        //   the published document is byte-identical to the base -- `(assume
        //   t0.a (and (not p) (= x x)))` bridged onto `(not p)` with `and_pos`
        //   (`folded_authored_conjunction_assume_is_the_problem_assertion`).
        // * `(assert (and (= a b) (= x x)))` + `(assert (not (= a b)))`: at the
        //   base this pass DECLINED that root and the query published `(error
        //   "proof was not generated for this independently certified result")`
        //   with no transport at all. Withheld, it publishes `(assume t0
        //   (= a b))` ... `(cl)` and the exported problem transport carries
        //   `(assert (= a b))`. Withholding is what lets that refutation be
        //   published, not a spelling this pass gives up.
        _ => return true,
    };
    let FrontendTerm::App(operator, _) = proof_surface_syntax::strip_frontend_annotations(source)
    else {
        return false;
    };
    operator == canonical_operator || is_comparison_reversal(operator, canonical_operator)
}

/// The one top-level head rewrite the printer bridges, with `comp_simplify`.
fn is_comparison_reversal(left: &str, right: &str) -> bool {
    matches!(
        (left, right),
        ("<=", ">=") | (">=", "<=") | ("<", ">") | (">", "<")
    )
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
    pub(in crate::executor::proof) fn purge_surface_overrides_for_certified_proof(
        &mut self,
        candidate: &Proof,
    ) {
        /// Work bound on the printed-term closure. An oversized reconstruction
        /// keeps today's spellings and simply stays unexportable.
        const MAX_PRINTED_TERMS: usize = 64 * 1024;

        let Some(mut overrides) = self.last_proof_term_overrides.clone() else {
            return;
        };

        let mut printed: DetHashSet<TermId> = DetHashSet::default();
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

    /// Build the replacement map transactionally. Identity/raw roots remove
    /// stale overrides; parsed roots must produce exactly one root spelling and
    /// may not conflict with an already authenticated spelling.
    fn restored_authored_override_map(
        &mut self,
        sources: Vec<ReachableAuthoredSource>,
    ) -> Option<(DetHashMap<TermId, String>, bool)> {
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        if !proof_surface_syntax::surface_override_map_is_bounded(&overrides) {
            return None;
        }
        let mut changed = false;
        for source in sources {
            let (root, source, replaces_stale) = match source {
                ReachableAuthoredSource::Identity(root) => {
                    changed |= overrides.remove(&root).is_some();
                    continue;
                }
                ReachableAuthoredSource::Untouched => continue,
                ReachableAuthoredSource::Parsed(root, source, replaces_stale) => {
                    (root, source, replaces_stale)
                }
            };
            let mut root_override = DetHashMap::default();
            proof_surface_syntax::collect_root_surface_term_override(
                &mut self.ctx,
                root,
                &source,
                &mut root_override,
            );
            let surface = root_override.remove(&root)?;
            if overrides
                .get(&root)
                .is_some_and(|existing| existing != &surface)
                && !replaces_stale
            {
                return None;
            }
            overrides.insert(root, surface);
            changed = true;
        }
        if changed && !proof_surface_syntax::surface_override_map_is_bounded(&overrides) {
            return None;
        }
        Some((overrides, changed))
    }

    /// Restore exact source spellings for reachable authored assumptions after
    /// every proof-replacement pass has finished.
    ///
    /// Certified reconstruction purges document-wide overrides so synthesized
    /// theory clauses retain the identity spelling the native checker
    /// validated. The Alethe printer nevertheless needs the problem file's
    /// exact spelling at each `assume`. This rebuilds only that narrow channel:
    /// every reachable canonical assumption must have one unique immutable
    /// `original_problem_assertions` index, paired with the parsed assertion at
    /// that same index. The only alternative is a separately interned raw root
    /// present in both `last_proof_rebuild_originals` (proof authority) and
    /// `last_proof_raw_original_assertions` (exact top-level source
    /// provenance), whose identity text is itself the authored spelling.
    /// Duplicate canonical roots publish an Alethe surface only when a row
    /// authenticates identity spelling or every emitted source spelling is
    /// identical. Other duplicate presentations suppress only Alethe; the
    /// independently checked native proof and portable bundle remain usable.
    pub(in crate::executor::proof) fn restore_reachable_authored_assume_surface_overrides(
        &mut self,
        proof: &Proof,
    ) {
        let Some(roots) = reachable_authored_assume_roots(proof) else {
            self.suppress_unsat_proof_reconstruction();
            return;
        };
        if roots.is_empty() {
            return;
        }

        // Retention-off certification intentionally has no authored text. It
        // may skip this presentation-only pass only when the query also has no
        // external proof demand. The policy bit plus the demand check is the
        // invariant that distinguishes that mode from a missing source ledger
        // on an artifact-producing query. In retained mode every reachable
        // assume needs an aligned source row, so empty or short ledgers fail
        // closed.
        if !self.ctx.retains_parsed_assertions() {
            if self.is_producing_proofs() || self.proof_artifact_required {
                self.suppress_unsat_proof_reconstruction();
            }
            return;
        }
        let sources = match self.resolve_reachable_authored_sources(&roots) {
            Ok(sources) => sources,
            Err(AuthoredSourceResolutionFailure::AletheSurfaceUnavailable) => return,
            Err(AuthoredSourceResolutionFailure::InvalidAuthority) => {
                self.suppress_unsat_proof_reconstruction();
                return;
            }
        };
        let Some((overrides, changed)) = self.restored_authored_override_map(sources) else {
            self.suppress_unsat_proof_reconstruction();
            return;
        };
        if changed {
            self.last_proof_term_overrides = Some(overrides);
        }
    }
}
