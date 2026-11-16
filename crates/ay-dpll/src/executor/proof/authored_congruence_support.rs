// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared support for authored congruence reconstruction and commit.

use super::*;
use crate::executor::{proof_surface_syntax, NATIVE_API_ASSERTION_PLACEHOLDER};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

#[path = "authored_congruence_support/confined_spelling.rs"]
mod confined_spelling;
use confined_spelling::{ConfinedSpelling, ConfinedSpellingKind};
#[path = "authored_congruence_support/source_resolution.rs"]
mod source_resolution;
use source_resolution::{AuthoredSourceResolutionFailure, ReachableAuthoredSource};

#[cfg(test)]
#[path = "authored_congruence_support/equality_expansion_tests.rs"]
mod equality_expansion_tests;
#[cfg(test)]
#[path = "authored_congruence_support/nra_sos_tests.rs"]
mod nra_sos_tests;

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
            | ProofStep::TheoryLemma { clause, .. }
            | ProofStep::FiniteFieldLinear { clause, .. }
            | ProofStep::NraSos { clause, .. } => clause.is_empty(),
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
            // SOS origin positions address literals within its own clause,
            // not proof steps; the certificate has no external premises.
            ProofStep::Assume(_)
            | ProofStep::TheoryLemma { .. }
            | ProofStep::FiniteFieldLinear { .. }
            | ProofStep::NraSos { .. } => {}
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
/// that root used to print the assume literal as an opaque `distinct` atom
/// while the resolution's other premise still printed `(= i j)`, and the
/// printer's own guard `surface_resolution_needs_distinct_bridge` correctly
/// refused the document with "a printed distinct/equality pivot cannot be
/// bridged to the authored operands". The printer now confines a BINARY
/// authored `distinct` over a canonical `(not (= x y))` to its own `assume`
/// with `distinct_elim` (+ `not_symm` when AY's argument order swapped the
/// pair) and prints the canonical literal everywhere else, so that head
/// rewrite is admitted below.
///
/// Withholding a spelling restores nothing and removes nothing: the root keeps
/// the canonical text `purge_surface_overrides_for_certified_proof` left, which
/// is NOT an assertion of the problem file `(get-proof)` is checked against.
/// MEASURED on `model_checker_consumer_quantified_models/signed_range64_fill_unsat.smt2`
/// before the `distinct` arm: the consequence-replay cascade published
/// `(assume t0 (not (= #b00000111 (select a #b1..1))))` for the authored
/// `(distinct (select a #xffffffffffffffff) #x07)`, the strict checker (which
/// compares interned roots) accepted it, and pinned carcara 1.1.0 refused the
/// document at `t0`: "could not match term to any of the original problem
/// premises". Every head rewrite the printer can bridge must therefore be
/// admitted here, not withheld.
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
        // * `(assert (and (= a b) (= x x)))` + `(assert (not (= a b)))`: at
        //   `dacc7939c7` this pass DECLINED that root and the query published
        //   `(error "proof was not generated for this independently certified
        //   result")` with no transport at all. Withheld (with nothing earlier
        //   on the root), it published `(assume t0 (= a b))` ... `(cl)` under
        //   `foreign_assumes=yes`, which pinned carcara 1.1.0 refused. The
        //   withheld root is now restored from its row when the printer
        //   derives the folded term from that exact spelling
        //   (`ReachableAuthoredSource::Folded`, `confined_spelling.rs`): here
        //   the conjunction projection `and_pos`, and the document is `valid`.
        _ => return true,
    };
    let FrontendTerm::App(operator, source_args) =
        proof_surface_syntax::strip_frontend_annotations(source)
    else {
        return false;
    };
    operator == canonical_operator
        || is_comparison_reversal(operator, canonical_operator)
        || is_binary_distinct_elimination(terms, root, operator, source_args.len())
        || is_equality_conjunction_expansion(terms, root, operator, source_args.len())
}

/// An authored binary equality whose canonical root is a conjunction of
/// binary equalities: a datatype equality `(= v7 v6)` that elaboration
/// expanded field by field into `(and (= v6!ptr v7!ptr) .. (= v6!data
/// v7!data))`. Withheld, the root published that expansion as its `assume`,
/// which is no assertion of the problem file. MEASURED on
/// `model_checker_consumer_quantified_counterexample/deep_vec_iteration_premise_false_unsat`:
/// `(assume t1 (and (= (ptr v6) (ptr v7)) ..))` and pinned carcara 1.1.0
/// refused the document at `t1` ("could not match term to any of the original
/// problem premises").
///
/// The printer confines the authored spelling with one `cong` per conjunct
/// when every conjunct is a unary congruence over the authored pair
/// (`alethe_printer/authored_assume/document_canonical.rs`), and declines
/// anything else -- a constructor equation expanded into selector VALUES is
/// related to its authored root only by the datatype theory, which pinned
/// carcara does not implement. A declined bridge leaves the authored spelling
/// document-wide, so the export is judged over the problem's own text and the
/// printer's step judgements refuse it rather than publish a premise the
/// problem never asserts. This is the head/arity admission only.
fn is_equality_conjunction_expansion(
    terms: &TermStore,
    root: TermId,
    operator: &str,
    arity: usize,
) -> bool {
    if operator != "=" || arity != 2 {
        return false;
    }
    let TermData::App(symbol, conjuncts) = terms.get(root) else {
        return false;
    };
    symbol.name() == "and"
        && !conjuncts.is_empty()
        && conjuncts.iter().all(|&conjunct| {
            matches!(
                terms.get(conjunct),
                TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2
            )
        })
}

/// The one negation-head rewrite the printer bridges, with `distinct_elim`:
/// a binary authored `(distinct a b)` whose canonical root is `(not (= x y))`.
/// The printer re-checks the operand pairing on the text it prints
/// (`alethe_printer/authored_assume/distinct.rs`) and declines the bridge on
/// any mismatch; this is only the head/arity admission.
fn is_binary_distinct_elimination(
    terms: &TermStore,
    root: TermId,
    operator: &str,
    arity: usize,
) -> bool {
    if operator != "distinct" || arity != 2 {
        return false;
    }
    let TermData::Not(equality) = terms.get(root) else {
        return false;
    };
    matches!(
        terms.get(*equality),
        TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2
    )
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
    /// stale root overrides here; their complete rendering is sealed after
    /// the final forall pass. Parsed roots must produce exactly one root
    /// spelling and may not conflict with an already authenticated spelling.
    ///
    /// Spellings installed only because the printer confines them are
    /// returned for the final re-judgement (`confined_spelling.rs`).
    fn restored_authored_override_map(
        &mut self,
        sources: Vec<ReachableAuthoredSource>,
    ) -> Option<(DetHashMap<TermId, String>, bool, Vec<ConfinedSpelling>)> {
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        if !proof_surface_syntax::surface_override_map_is_bounded(&overrides) {
            return None;
        }
        let mut changed = false;
        let mut confined = Vec::new();
        for source in sources {
            let (root, source, replaces_stale) = match source {
                ReachableAuthoredSource::Identity(root)
                | ReachableAuthoredSource::RawIdentity(root) => {
                    changed |= overrides.remove(&root).is_some();
                    continue;
                }
                ReachableAuthoredSource::Untouched => continue,
                ReachableAuthoredSource::Folded(root, source) => {
                    changed |=
                        self.install_folded_spelling(root, &source, &mut overrides, &mut confined);
                    continue;
                }
                ReachableAuthoredSource::ExpandedLet(root, surface) => {
                    if overrides
                        .get(&root)
                        .is_some_and(|existing| existing != &surface)
                    {
                        return None;
                    }
                    overrides.insert(root, surface);
                    changed = true;
                    continue;
                }
                ReachableAuthoredSource::Parsed(root, source, replaces_stale) => {
                    (root, source, replaces_stale)
                }
            };
            let (surface, guarded) =
                self.parsed_root_spelling(root, &source, overrides.get(&root), replaces_stale)?;
            let previous = overrides.insert(root, surface);
            if guarded {
                confined.push(ConfinedSpelling {
                    root,
                    previous,
                    kind: ConfinedSpellingKind::Guarded,
                });
            } else {
                self.spell_connective_quantifier_operand(root, &source, &mut overrides);
            }
            changed = true;
        }
        if changed && !proof_surface_syntax::surface_override_map_is_bounded(&overrides) {
            return None;
        }
        Some((overrides, changed, confined))
    }

    /// The universal operand of an authored `(= A F)` / `(=> A F)` root whose
    /// whole spelling was just installed: without its own spelling (and its
    /// body's, under the recovered binder), the root prints the authored
    /// universal while every step that reasons about the universal
    /// (`equiv_pos2`, `implies_pos`, `forall_inst`) prints the canonical one,
    /// and the export is refused (`no equiv_pos2 instance over the printed
    /// surface reproduces this clause`). MEASURED on w1_51 file 121. The
    /// ordinary override plan never spells this universal (it declines any
    /// root with a binder below a non-quantifier head), so this pass is the
    /// only one that does (#iff-split-implied-authority). The entries are
    /// keyed on the
    /// quantifier and on terms under its binder, so no ground step of an
    /// independently certified theory lemma is re-spelled; a quantifier past
    /// the collection bound keeps its canonical text and the printer judges
    /// the result.
    fn spell_connective_quantifier_operand(
        &mut self,
        root: TermId,
        source: &FrontendTerm,
        overrides: &mut DetHashMap<TermId, String>,
    ) {
        let Some((quantifier, parsed)) =
            proof_surface_syntax::connective_quantifier_pair(&self.ctx.terms, root, source)
        else {
            return;
        };
        let parsed = parsed.clone();
        let _bounded = proof_surface_syntax::collect_surface_term_overrides(
            &mut self.ctx,
            quantifier,
            &parsed,
            overrides,
        );
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
    ///
    /// Every installer that REPLACES `last_proof` after this pass ran owes the
    /// same restoration for the proof it installs; the native SOS lane calls
    /// it from its bind (see `native_nra_sos.rs`).
    pub(in crate::executor) fn restore_reachable_authored_assume_surface_overrides(
        &mut self,
        proof: &Proof,
    ) {
        let Some(roots) = reachable_authored_assume_roots(proof) else {
            self.suppress_unsat_proof_reconstruction();
            // #evidence-stage-3, second pass. Every suppression in this
            // function keeps a DERIVATION and drops only its authored-scope
            // spelling, which is a different repair from every producer-side
            // decline and was indistinguishable from them in the census.
            self.record_proof_decline(ProofDeclineMechanism::AuthoredAssumeSurfaceUnavailable);
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
                self.record_proof_decline(ProofDeclineMechanism::RetentionOffWithoutAuthoredText);
            }
            return;
        }
        let sources = match self.resolve_reachable_authored_sources(&roots) {
            Ok(sources) => self.respell_nullary_macro_raw_roots(sources),
            Err(AuthoredSourceResolutionFailure::AletheSurfaceUnavailable) => return,
            Err(AuthoredSourceResolutionFailure::InvalidAuthority) => {
                self.suppress_unsat_proof_reconstruction();
                self.record_proof_decline(ProofDeclineMechanism::AuthoredSourceAuthorityInvalid);
                return;
            }
        };
        let authored_foralls = authored_forall_sources(&self.ctx.terms, &sources);
        let identity_roots: Vec<TermId> = sources
            .iter()
            .filter_map(ReachableAuthoredSource::canonical_row_root)
            .collect();
        let Some((mut overrides, mut changed, confined)) =
            self.restored_authored_override_map(sources)
        else {
            self.suppress_unsat_proof_reconstruction();
            self.record_proof_decline(ProofDeclineMechanism::AuthoredAssumeSurfaceUnavailable);
            return;
        };
        changed |=
            self.spell_forall_instances_on_final_proof(proof, &authored_foralls, &mut overrides);
        // A later Parsed root or forall instance can re-spell a descendant
        // of an earlier Identity root. Seal only after both passes finish.
        let Some(sealed) = self.seal_authored_identity_surfaces(&identity_roots, &mut overrides)
        else {
            self.suppress_unsat_proof_reconstruction();
            self.record_proof_decline(ProofDeclineMechanism::AuthoredAssumeSurfaceUnavailable);
            return;
        };
        changed |= sealed;
        // Only the finished map says which descendants are re-spelled
        // document-wide, and the printer declines a fold bridge above one.
        let Some(withdrawn) = self.withdraw_unconfined_spellings(proof, confined, &mut overrides)
        else {
            self.suppress_unsat_proof_reconstruction();
            self.record_proof_decline(ProofDeclineMechanism::AuthoredAssumeSurfaceUnavailable);
            return;
        };
        changed |= withdrawn;
        if changed {
            self.last_proof_term_overrides = Some(overrides);
        }
    }

    /// Give every `forall_inst` of the FINAL proof the exact source spelling
    /// of its instance, where the instantiated quantifier is a reachable
    /// authored root.
    ///
    /// The ordinary pass (`add_forall_instance_surface_overrides`) runs inside
    /// `apply_input_syntax_rewrites_to_proof`, on the proof as it stood
    /// BEFORE the rebuild lanes of `finish_input_syntax_rewrite` and the
    /// authored replacement cascade. A lane that replaces the proof purges
    /// every spelling of a term its candidate prints
    /// (`purge_surface_overrides_for_certified_proof`) and re-collects only
    /// the authored ROOTS and their subterms; a `forall_inst` instance is a
    /// distinct `TermId` the collector never visits, so it reaches the
    /// printer with its CANONICAL rendering under an AUTHORED quantifier —
    /// `(< c (f c))` under `(forall ((w Int)) (> (f w) w))`. MEASURED
    /// 2026-09-13 on the eighth false green's `sko_ex` sibling: on main that
    /// step shipped as `forall_inst` under a green flag and pinned carcara
    /// refused it (`expected term .. to be ..`); after the printed
    /// `forall_inst` judgement it declines to an honest `hole`. This pass is
    /// what makes the derivation, which exists, printable: the same
    /// rendering the ordinary pass produces, computed over the proof that
    /// ships.
    ///
    /// Semantics are the ordinary pass's, restricted to what it has not
    /// already decided: an instance that carries a spelling from an earlier
    /// pass keeps it (today's documents are byte-identical), an instance
    /// spelled twice by THIS pass with two different texts is the same
    /// conflict the ordinary pass declines (`ForallInstanceSurfaceConflict`),
    /// and the printer's own `forall_inst` judgement still reads the bytes
    /// that ship, so nothing here can turn a mismatch into a claim. Unlike
    /// the ordinary pass, an instance the store folded to a variable or
    /// constant under a composite authored body keeps its canonical text
    /// (`forall_instance_would_hijack_atom`): this pass also runs for the
    /// expansion certificate, whose `(forall ((q Bool)) (and q q))` instance
    /// is the shared `false`.
    ///
    /// Returns whether `overrides` changed.
    fn spell_forall_instances_on_final_proof(
        &mut self,
        proof: &Proof,
        authored_foralls: &DetHashMap<TermId, FrontendTerm>,
        overrides: &mut DetHashMap<TermId, String>,
    ) -> bool {
        if authored_foralls.is_empty() {
            return false;
        }
        let mut changed = false;
        let mut spelled_here: DetHashSet<TermId> = DetHashSet::default();
        let debug = ay_core::misc_cli_flags().debug_cert;
        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::Step {
                rule: AletheRule::ForallInst,
                clause,
                args,
                ..
            } = step
            else {
                continue;
            };
            let [implication] = clause.as_slice() else {
                continue;
            };
            let TermData::App(Symbol::Named(name), disjuncts) = self.ctx.terms.get(*implication)
            else {
                continue;
            };
            if name != "or" || disjuncts.len() != 2 {
                continue;
            }
            let TermData::Not(quantifier) = self.ctx.terms.get(disjuncts[0]) else {
                continue;
            };
            let Some(parsed) = authored_foralls.get(quantifier) else {
                continue;
            };
            let instance = disjuncts[1];
            if overrides.contains_key(&instance) && !spelled_here.contains(&instance) {
                // An earlier pass already spelled this instance; its decision
                // stands, and the printed judgement reads the result.
                continue;
            }
            if proof_surface_syntax::forall_instance_would_hijack_atom(
                &self.ctx.terms,
                instance,
                parsed,
            ) {
                // A composite body folded to a shared atom: the entry would
                // re-spell every occurrence of it (the `false` axiom first).
                continue;
            }
            let Some(surface) = proof_surface_syntax::format_forall_instance_surface(
                &self.ctx.terms,
                parsed,
                args,
                overrides,
            ) else {
                if debug {
                    ay_core::safe_eprintln!(
                        "c !! final forall-inst surface at t{index}: authored body does not render under the substitution"
                    );
                }
                self.decline_forall_instance_surface();
                return changed;
            };
            if let Some(existing) = overrides.get(&instance) {
                if existing != &surface {
                    if debug {
                        ay_core::safe_eprintln!(
                            "c !! final forall-inst surface at t{index}: instance already spelled another way"
                        );
                    }
                    self.decline_forall_instance_surface();
                    return changed;
                }
                continue;
            }
            if debug {
                ay_core::safe_eprintln!("c !! final forall-inst surface at t{index}: {surface}");
            }
            overrides.insert(instance, surface);
            spelled_here.insert(instance);
            changed = true;
            if !proof_surface_syntax::surface_override_map_is_bounded(overrides) {
                self.decline_forall_instance_surface();
                return changed;
            }
        }
        changed
    }

    /// A `forall_inst` instance with no faithful authored spelling withholds
    /// the whole reconstruction rather than print a guess.
    fn decline_forall_instance_surface(&mut self) {
        self.suppress_unsat_proof_reconstruction();
        self.record_proof_decline(ProofDeclineMechanism::ForallInstanceSurfaceConflict);
    }
}

/// The reachable authored roots that are `forall` assertions, paired with
/// their parsed source: the quantifiers whose `forall_inst` instances
/// [`Executor::spell_forall_instances_on_final_proof`] can spell.
fn authored_forall_sources(
    terms: &TermStore,
    sources: &[ReachableAuthoredSource],
) -> DetHashMap<TermId, FrontendTerm> {
    sources
        .iter()
        .filter_map(|source| match source {
            ReachableAuthoredSource::Parsed(root, parsed, _) => {
                proof_surface_syntax::authored_forall_of_root(terms, *root, parsed)
                    .map(|(forall, parsed)| (forall, parsed.clone()))
            }
            _ => None,
        })
        .collect()
}
