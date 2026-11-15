// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Record the argument behind a preprocessor fold-to-`false` whose cause is
//! visible on the authored conjunction itself: a NORMALIZATION IDENTITY (an
//! authored disequality whose two operands are one term once the term
//! store's arithmetic normalization has run), or a PROPOSITIONAL COMPLEMENT
//! (a conjunct and its negation).
//!
//! ## The class, as measured
//!
//! QF_UFLIA `mathsat/Hash/hash_uns_*` — all 54 files of the family — end in
//! the conjunct
//!
//! ```text
//! (distinct (ite ?v_k ?v_3 (+ ?v_0 ?v_0)) (ite ?v_k ?v_3 (* 2 ?v_0)))
//! ```
//!
//! under two `let` levels. Elaboration normalizes `(+ ?v_0 ?v_0)` to
//! `(* 2 ?v_0)`, hash-consing then makes the two `ite`s ONE term, `mk_distinct`
//! folds `(distinct t t)` to `false`, the enclosing `and` folds with it, and
//! `ctx.assertions` holds the constant `false` with no record of the rewrite.
//! `false_source::demote_unattributed_assumed_false` erases the proof to
//! `(step t0 (cl) :rule hole)` — the `preprocessor-fold-to-false` decline the
//! 2026-09-12 headline sweep attributed to 6 of its 59 refutations. The same
//! erasure hides QF_AX `swap_t2_np_nf_ai_00002_001` (`(not (= ?v_3 ?v_3))`
//! under four `let` levels: reflexivity), QF_LRA `polypaver-bench-exp-3d
//! chunk-0145` (`(and (not ?v_0) (and ?v_0 ..))`: a complement) and QF_BVFP
//! `klee query.2121` (`(not (not (and (not $x50) $x50)))`: the same
//! complement under a double negation).
//!
//! None of the three sibling promoters can see any of them. The authored
//! root is `let`-rooted, so `authored_conjunct_eval` refuses it at its first
//! check (`FrontendTerm::App` only) and `raw_intern_surface` fails closed on
//! the binder; the BV/LIA interpreter needs a CLOSED assertion and these are
//! over uninterpreted applications; and there is no shared quantifier.
//!
//! ## The derivation
//!
//! The fold's own argument is that `A` and `B` are equal (or that `L` and
//! `(not L)` are both conjuncts), and that argument is expressible with
//! standard Alethe rules the pinned external checker carries and AY's strict
//! checker re-derives:
//!
//! ```text
//! (assume h0 <authored root, let-rooted text verbatim>)
//!   ... the printer's own let bridge: refl / let / equiv_pos2 / resolution
//!       to the eliminated form, exactly as for every other let-rooted assume
//! (step t1 (cl (not ROOT) (distinct A B)) :rule and_pos)      ; per and-level
//! (step t2 (cl (distinct A B)) :rule resolution)
//! (step t3 (cl (<= X Y)) :rule la_generic :args (1))           ; X = (+ v v)
//! (step t4 (cl (<= Y X)) :rule la_generic :args (1))           ; Y = (* 2 v)
//! (step t5 (cl (or (= X Y) (not (<= X Y)) (not (<= Y X)))) :rule la_disequality)
//! (step t6 (cl (= X Y) (not (<= X Y)) (not (<= Y X))) :rule or)
//! (step t7 (cl (= X Y)) :rule resolution)
//! (step t8 (cl (= c c)) :rule refl)  (step t9 (cl (= a a)) :rule refl)
//! (step t10 (cl (= A B)) :rule cong :premises (t8 t9 t7))
//! (step t11 (cl (= (distinct A B) (not (= A B)))) :rule distinct_elim)
//! (step t12 (cl (not (= (distinct A B) (not (= A B)))) (not (distinct A B)) (not (= A B))) :rule equiv_pos2)
//! (step t13 (cl (not (= A B))) :rule resolution)
//! (step t14 (cl) :rule resolution :premises (t13 t10))
//! ```
//!
//! The identity is decided the way the fold decided it: the two parsed
//! operands are RE-ELABORATED through the ordinary (folding) elaborator and
//! must come back as one `TermId`. The derivation of `(= A B)` then never
//! re-implements the normalization: it is a `cong` decomposition down to the
//! arithmetic leaves that differ, and at each such leaf a Farkas-annotated
//! `la_generic` pair (`X <= Y` and `Y <= X`, coefficient 1 each, which the
//! strict LIA validator re-verifies semantically) joined by `la_disequality`.
//! A complement is two `and_pos` projections and one resolution; a root
//! under exactly one `(not (not ..))` shell pair is projected by resolving
//! the shelled assume against `and_pos` on the pivot `(not ROOT)`, which
//! needs no rule the checkers do not already have. Everything is re-derived
//! by the checker; nothing is taken on this pass's word.
//!
//! A complement the `and`-spine cannot reach — under an `or` the elaborator
//! collapsed, beside `false` disjuncts or `true` conjuncts, under a negated
//! connective — is the PROPOSITIONAL argument
//! (`authored_fold_identity_propositional`), tried last on an unshelled root
//! and committed through the same gates below.
//!
//! ## What keeps this honest
//!
//! 1. The single `assume` is the author's own assertion. A `let`-rooted root
//!    is expanded on the PARSE TREE with SMT-LIB's parallel semantics (the
//!    capture-safe `expand_surface_lets` the printer's source resolution
//!    re-runs), re-interned RAW so the folding constructors cannot touch it,
//!    registered as an expanded-`let` source exactly as `and_collapse` does,
//!    and then rendered through the exporter's printer and re-parsed until it
//!    is the author's parsed assertion again (`rebuilt_root_prints_as_authored`).
//!    A premise that cannot be matched to a problem assertion is the one
//!    outcome strictly worse than the hole.
//! 2. Nothing is taken on the producer's word. The UNCHANGED strict checker
//!    must accept the whole candidate as COMPLETE, the exporter's own
//!    authority check must accept its `assume` against the exporter's own
//!    premise set, and the exporter itself must render the document, before
//!    anything is committed. Any decline restores every ledger this pass
//!    touched and the erasure proceeds exactly as before.
//! 3. `--no-authored-fold-identity` disables the pass; with it set the
//!    decline is byte-identical to the baseline.
//!
//! ## Cost, and why it runs first
//!
//! The three sibling promoters each charge FOUR source-scale passes against
//! the query's aggregate envelope before they look at a root, then refuse a
//! `let`-rooted one at their first structural check. Measured on
//! `hash_uns_03_18` (6.6 KB, an `and`-chain 100 deep): one pass is 2.8 MB
//! of the 32 MB envelope, and by the time the erasure reached this pass
//! 2.7 MB were left. So this pass is charged PER CANDIDATE ROOT, in two
//! stages — one pass for the scan that decides whether an argument exists at
//! all, and three more only when one does — after a free by-reference shape
//! scan that skips every root with no disequality or negated conjunct. It
//! runs before its siblings because on a root they cannot act on it is the
//! only pass that can, and on every other root its scan stage costs the
//! envelope a single pass.
//!
//! ## What it does NOT close (measured, 2026-09-12)
//!
//! The same family at depth: `hash_uns_03_09` and above have an `and`-chain
//! deeper than the printer's authored-assume bound (`MAX_EQUIVALENCE_DEPTH`,
//! 64), so the render gate declines and the bare hole stays — 46 of the 54
//! files, a rendering limit and not this pass's. An array store-permutation
//! identity (QF_AUFLIA `storecomm`) is recognised as an identity but has no
//! closer here (the operands are `store` chains, not arithmetic). Datatype
//! tester evaluation has no rule in pinned carcara 1.1.0 at all.

use ay_core::term::TermData;
use ay_core::{
    AletheRule, FarkasAnnotation, Proof, ProofId, Sort, Symbol, TermId, TheoryLemmaKind,
};
use ay_frontend::command::Term as FrontendTerm;

use super::Executor;
use crate::executor::proof_repair::proof_trust_surgery::surface_terms::expand_surface_lets;
use crate::executor::proof_repair::proof_trust_surgery_surface_audit::ProofSourcePass;
use crate::executor::proof_surface_syntax::{format_frontend_term, strip_frontend_annotations};
use crate::executor::proof_trust_surgery_provenance::MAX_PROVENANCE_REPAIR_TERMS;

/// Parsed roots inspected per query. The fold this recovers is decided at
/// parse time on one authored root; a problem with more roots than this is
/// not the class and the erasure proceeds untouched.
const MAX_FOLD_IDENTITY_ROOTS: usize = 64;
/// Candidate roots the shape scan may hand to the charged stages.
const MAX_CANDIDATE_ROOTS: usize = 8;
/// Upper bound on conjunct nodes inspected per authored root — the same
/// second, independent stop `authored_conjunct_eval` applies.
const MAX_SCANNED_CONJUNCT_NODES: usize = 8_192;
/// Nodes the `cong` decomposition of one disequality may visit.
const MAX_DIFF_NODES: usize = 512;
/// Conjuncts the complement pairing may compare pairwise. The pairing is
/// quadratic in the conjunct count; above this it is simply not attempted
/// (the identity scan, which is linear, still is).
const MAX_PAIRED_CONJUNCTS: usize = 256;

/// One argument the fold had, located by child-index paths from the body's
/// outermost `and`.
enum FoldArgument {
    /// `(distinct A B)` or `(not (= A B))` at `path`, with `A` and `B` one
    /// canonical term.
    Identity(Vec<u32>),
    /// A conjunct `L` at `positive` and `(not L)` at `negative`.
    Complement {
        positive: Vec<u32>,
        negative: Vec<u32>,
    },
    /// The root is false by its Boolean skeleton through `and` / `or` /
    /// negated connectives at any depth
    /// (`authored_fold_identity_propositional`). Tried last, and only on an
    /// unshelled root.
    Propositional,
}

/// A conjunct of the raw `and`-tree beside its parsed form.
struct Conjunct<'a> {
    path: Vec<u32>,
    term: TermId,
    parsed: &'a FrontendTerm,
}

/// The disequality conjunct an identity refutes, in both forms.
struct DisequalityLeaf {
    path: Vec<u32>,
    leaf: TermId,
    /// `(distinct A B)` when `true`; `(not (= A B))` otherwise.
    distinct: bool,
    lhs: TermId,
    rhs: TermId,
    parsed_lhs: FrontendTerm,
    parsed_rhs: FrontendTerm,
}

impl Executor {
    /// Replace a proof that rests on an unattributed `assume false` with the
    /// derivation the fold actually had. `true` when a strictly-checked,
    /// export-authorized, renderable replacement was committed.
    pub(super) fn replace_with_exact_authored_fold_identity_refutation(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        if !crate::quant_unit_authority::authored_fold_identity_enabled() {
            return false;
        }
        let parsed = self.ctx.assertions_parsed();
        if parsed.is_empty() || parsed.len() > MAX_FOLD_IDENTITY_ROOTS {
            return false;
        }
        // Free, by-reference shape scan: only a root with a disequality or a
        // negated conjunct under its `and`-spine (through any `let` levels)
        // can be this class. Nothing is cloned and nothing is charged for a
        // root that is not.
        // The conjunct-spine candidates keep their slots ahead of the
        // propositional-only ones, so the wider scan can never crowd a root
        // the original argument closes out of the candidate bound.
        let mut candidates: Vec<usize> = parsed
            .iter()
            .enumerate()
            .filter(|(_, assertion)| parsed_root_holds_candidate_conjunct(assertion))
            .map(|(index, _)| index)
            .take(MAX_CANDIDATE_ROOTS)
            .collect();
        let propositional: Vec<usize> = parsed
            .iter()
            .enumerate()
            .filter(|(index, assertion)| {
                !candidates.contains(index) && parsed_root_holds_propositional_candidate(assertion)
            })
            .map(|(index, _)| index)
            .take(MAX_CANDIDATE_ROOTS.saturating_sub(candidates.len()))
            .collect();
        candidates.extend(propositional);
        for index in candidates {
            let assertion = self.ctx.assertions_parsed()[index].clone();
            // Stage 1, charged against the SAME query-local envelope every
            // other source-touching pass shares: the clone above, the `let`
            // expansion and the argument scan — one source-scale pass over
            // THIS root.
            if !self.proof_source_work.spend(
                ProofSourcePass::AuthoredFoldIdentityScan,
                std::iter::once(&assertion),
            ) {
                super::authored_consequence_replay::replay_note(|| {
                    format!(
                        "[fold-identity] scan stage refused by the source envelope ({} left)",
                        self.proof_source_work.remaining()
                    )
                });
                return false;
            }
            if self.try_authored_fold_identity_refutation(proof, index, &assertion) {
                return true;
            }
        }
        false
    }

    fn try_authored_fold_identity_refutation(
        &mut self,
        proof: &mut Proof,
        source_index: usize,
        assertion: &FrontendTerm,
    ) -> bool {
        let authored = strip_frontend_annotations(assertion);
        let let_rooted = matches!(authored, FrontendTerm::Let(..));
        // The binder-free view of the root. A `let`-rooted assertion is
        // expanded on the parse tree with SMT-LIB's parallel semantics (the
        // same capture-safe expansion the printer's source resolution will
        // re-run to authenticate the root); anything else is used as written.
        let Some(expanded) = expand_surface_lets(authored, &std::collections::HashMap::new())
        else {
            return false;
        };
        let expanded = strip_frontend_annotations(&expanded).clone();
        // Only an application can carry the conjunct this pass looks for, and
        // `raw_intern_surface` fails closed on anything it cannot rebuild
        // node-by-node.
        if !matches!(expanded, FrontendTerm::App(..)) {
            return false;
        }
        // The body under exactly one authored `(not (not ..))` shell pair, or
        // the root itself.
        let (parsed_body, shelled) = peel_one_negation_pair(&expanded);
        // Stage 1: does the body hold an argument at all — a disequality
        // whose operands re-elaborate, through the ordinary folding
        // elaborator, to ONE canonical term (exactly the identity the fold
        // rested on, decided the way the fold decided it), or a conjunct and
        // its negation? No interning of the root happens before this answers.
        let Some(parsed_conjuncts) = parsed_conjuncts(parsed_body) else {
            return false;
        };
        let mut arguments = self.fold_arguments(&parsed_conjuncts);
        if !shelled && parsed_root_holds_propositional_candidate(&expanded) {
            arguments.push(FoldArgument::Propositional);
        }
        if arguments.is_empty() {
            super::authored_consequence_replay::replay_note(|| {
                format!(
                    "[fold-identity] no identity or complement among {} conjuncts",
                    parsed_conjuncts.len()
                )
            });
            return false;
        }
        // Stage 2: the raw re-intern, the override-aware round trip and the
        // render gate — three more source-scale passes over this root.
        if !self.proof_source_work.spend(
            ProofSourcePass::AuthoredFoldIdentityRebuild,
            std::iter::once(assertion),
        ) {
            super::authored_consequence_replay::replay_note(|| {
                format!(
                    "[fold-identity] rebuild stage refused by the source envelope ({} left)",
                    self.proof_source_work.remaining()
                )
            });
            return false;
        }
        let Some(root) = self.raw_intern_surface(&expanded) else {
            super::authored_consequence_replay::replay_note(|| {
                "[fold-identity] raw_intern_surface declined the expanded root".into()
            });
            return false;
        };
        if !matches!(self.ctx.terms.sort(root), Sort::Bool) {
            return false;
        }
        // The raw body: the root, or the term under its two raw `not` nodes.
        let body = if shelled {
            let Some(body) = self.raw_double_negation_body(root) else {
                return false;
            };
            body
        } else {
            root
        };

        // Every ledger this pass touches is snapshotted here and restored on
        // EVERY decline, so a pass that does not commit leaves the executor
        // byte-identical to how it found it.
        let saved_overrides = self.last_proof_term_overrides.clone();
        let saved_premises = self.last_proof_rebuild_originals.clone();
        let saved_raw_originals = self.last_proof_raw_original_assertions.clone();
        let saved_let_sources = self.last_proof_expanded_let_sources.clone();
        let restore = |executor: &mut Self| {
            executor.last_proof_term_overrides = saved_overrides.clone();
            executor.last_proof_rebuild_originals = saved_premises.clone();
            executor.last_proof_raw_original_assertions = saved_raw_originals.clone();
            executor.last_proof_expanded_let_sources = saved_let_sources.clone();
        };

        // A `let`-rooted assertion must PRINT as the author's `(let ...)`: the
        // external checker matches a let-rooted premise only through `let`
        // (the printer's `format_let_assume_bridge` records the measurement).
        // Register the raw root as an EXPANDED-LET source — the ledger the
        // printer's source resolution authenticates by re-expanding the parsed
        // row and demanding the root's own canonical text back — exactly as
        // `and_collapse`'s `ExpandedLet` bridge does. The printer then
        // discharges the elimination itself with `refl`/`let`. The round-trip
        // gate below re-parses the result and demands the authored assertion
        // back.
        if let_rooted && !self.install_expanded_let_source(root, source_index, authored, &expanded)
        {
            restore(self);
            return false;
        }
        let exact_spelling = self.rebuilt_root_prints_as_authored(root, assertion)
            || self.try_raw_descendant_spellings(root, assertion);
        let propositional_literal_spelling = !exact_spelling
            && !let_rooted
            && arguments
                .iter()
                .any(|argument| matches!(argument, FoldArgument::Propositional))
            && self.raw_propositional_literal_roundtrip(root, assertion);
        if !exact_spelling && !propositional_literal_spelling {
            super::authored_consequence_replay::replay_note(|| {
                let overrides = self.proof_export_term_overrides().unwrap_or_default();
                format!(
                    "[fold-identity] rebuilt root does not print as authored: {}",
                    ay_proof::format_term_alethe_with_overrides(&self.ctx.terms, root, &overrides)
                )
            });
            restore(self);
            return false;
        }

        let Some(conjuncts) = self.raw_conjuncts(body, parsed_body) else {
            restore(self);
            return false;
        };
        for argument in &arguments {
            if !exact_spelling && !matches!(argument, FoldArgument::Propositional) {
                continue;
            }
            let Some(candidate) =
                self.fold_argument_candidate(root, body, shelled, &conjuncts, argument)
            else {
                super::authored_consequence_replay::replay_note(|| {
                    "[fold-identity] argument found but no derivation was built".into()
                });
                continue;
            };
            // Only now is `root` known to BE the author's assertion, re-interned
            // raw from its parsed surface; record it as one. Both ledgers are
            // needed (proof authority, and exact raw problem provenance for the
            // printer's authored-source resolution).
            self.record_raw_authored_problem_assertion(root);
            // DERIVATION. The UNCHANGED strict checker is the only authority
            // that commits this.
            let strict = self.check_proof_strict_with_datatypes(&candidate);
            if !Self::proof_derives_empty_clause(&candidate)
                || !strict.as_ref().is_ok_and(|quality| quality.is_complete())
            {
                super::authored_consequence_replay::replay_note(|| {
                    format!(
                        "[fold-identity] strict check refused the candidate: {:?}",
                        strict
                            .as_ref()
                            .map(|quality| quality.is_complete())
                            .map_err(|error| error.to_string())
                    )
                });
                restore(self);
                return false;
            }
            // EXPORT AUTHORITY. The strict checker's premise set is a strict
            // superset of the exporter's.
            if ay_proof::validate_reachable_assumes_in_problem_scope(
                &candidate,
                &self.proof_export_scope_assertions(),
            )
            .is_err()
            {
                restore(self);
                return false;
            }
            // RENDER. A candidate every other gate accepts can still be
            // refused by the printer, and under `--proof FILE` that refusal
            // publishes NO verdict at exit 1. Run the exporter itself.
            if !self.fold_identity_candidate_renders(&candidate) {
                restore(self);
                return false;
            }
            *proof = candidate;
            return true;
        }
        restore(self);
        false
    }

    /// Every argument the parsed body holds: identity leaves first (they are
    /// the measured class), then complements.
    fn fold_arguments(&mut self, conjuncts: &[(Vec<u32>, &FrontendTerm)]) -> Vec<FoldArgument> {
        let mut arguments = Vec::new();
        for (path, parsed) in conjuncts {
            let Some((_, lhs, rhs)) = parsed_disequality(parsed) else {
                continue;
            };
            let lhs = self.ctx.elaborate_surface_subterm(lhs);
            if lhs.is_some() && lhs == self.ctx.elaborate_surface_subterm(rhs) {
                arguments.push(FoldArgument::Identity(path.clone()));
            }
        }
        if conjuncts.len() > MAX_PAIRED_CONJUNCTS {
            return arguments;
        }
        for (negative_path, parsed) in conjuncts {
            let FrontendTerm::App(name, args) = parsed else {
                continue;
            };
            if name != "not" || args.len() != 1 {
                continue;
            }
            let inner = strip_frontend_annotations(&args[0]);
            if let Some((positive_path, _)) = conjuncts
                .iter()
                .find(|(_, candidate)| strip_frontend_annotations(candidate) == inner)
            {
                arguments.push(FoldArgument::Complement {
                    positive: positive_path.clone(),
                    negative: negative_path.clone(),
                });
            }
        }
        arguments
    }

    /// The term under a raw root of the exact shape `(not (not body))`.
    fn raw_double_negation_body(&self, root: TermId) -> Option<TermId> {
        let TermData::Not(outer) = self.ctx.terms.get(root) else {
            return None;
        };
        let TermData::Not(inner) = self.ctx.terms.get(*outer) else {
            return None;
        };
        Some(*inner)
    }

    /// Register the raw root as the capture-safe expansion of the authored
    /// `let` row at `source_index`, in the exact shape
    /// `resolve_reachable_authored_sources` authenticates: the row must be a
    /// `let`, its expansion must print byte-identically to the root's own
    /// canonical text, and the root's override must be the row's surface.
    /// An override changes how a term PRINTS, never what it is or what may be
    /// assumed; the printer re-derives the elimination with `refl`/`let`.
    fn install_expanded_let_source(
        &mut self,
        root: TermId,
        source_index: usize,
        authored: &FrontendTerm,
        expanded: &FrontendTerm,
    ) -> bool {
        let source_surface = format_frontend_term(authored);
        if !source_surface.starts_with("(let") {
            return false;
        }
        // The raw root must BE the expansion, textually: this is the
        // authentication the source resolution re-runs at export, and a root
        // that fails it there is refused as `authored-source-authority-invalid`
        // after every other gate has passed.
        if format_frontend_term(expanded) != ay_proof::format_term_alethe(&self.ctx.terms, root) {
            super::authored_consequence_replay::replay_note(|| {
                "[fold-identity] expanded let row does not print as the raw root".into()
            });
            return false;
        }
        let source = (root, source_index, source_surface.clone());
        if self.last_proof_expanded_let_sources.len() >= MAX_PROVENANCE_REPAIR_TERMS
            && !self.last_proof_expanded_let_sources.contains(&source)
        {
            return false;
        }
        if self
            .last_proof_expanded_let_sources
            .iter()
            .any(|(other, index, surface)| {
                *other == root && (*index != source_index || *surface != source_surface)
            })
        {
            return false;
        }
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        if overrides
            .get(&root)
            .is_some_and(|existing| *existing != source_surface)
        {
            return false;
        }
        overrides.insert(root, source_surface);
        if !crate::executor::proof_surface_syntax::surface_override_map_is_bounded(&overrides) {
            return false;
        }
        self.last_proof_term_overrides = Some(overrides);
        if !self.last_proof_expanded_let_sources.contains(&source) {
            self.last_proof_expanded_let_sources.push(source);
        }
        true
    }

    /// Does the EXPORTER accept this candidate? Same call, same scope, same
    /// overrides and authored shells the CLI's own Alethe export makes.
    fn fold_identity_candidate_renders(&self, candidate: &Proof) -> bool {
        let Some(scope) = self.proof_export_scope_assertions_for(candidate) else {
            return false;
        };
        let overrides = self.proof_export_term_overrides();
        let shells = self.authored_negation_shell_spellings().bridgeable;
        let rendered = self.in_alethe_dialect(|| {
            ay_proof::try_export_alethe_with_authored_assume_shells(
                candidate,
                &self.ctx.terms,
                &scope,
                overrides.as_ref(),
                (!shells.is_empty()).then_some(&shells),
                Some(super::DEFAULT_ALETHE_EMISSION_WORK_BUDGET),
            )
        });
        if let Err(error) = &rendered {
            super::authored_consequence_replay::replay_note(|| {
                format!("[fold-identity] the exporter refused the candidate: {error}")
            });
        }
        rendered.is_ok()
    }

    /// Every conjunct of the raw `and`-tree rooted at `body`, walked in
    /// lockstep with the parsed body so each carries its parsed form. `None`
    /// when the two trees disagree in shape or the walk exceeds its bound.
    fn raw_conjuncts<'a>(
        &self,
        body: TermId,
        parsed: &'a FrontendTerm,
    ) -> Option<Vec<Conjunct<'a>>> {
        let mut conjuncts = Vec::new();
        let mut stack: Vec<(TermId, &'a FrontendTerm, Vec<u32>)> = vec![(body, parsed, Vec::new())];
        let mut visited = 0usize;
        while let Some((term, parsed, path)) = stack.pop() {
            visited += 1;
            if visited > MAX_SCANNED_CONJUNCT_NODES {
                return None;
            }
            let parsed = strip_frontend_annotations(parsed);
            if let (
                TermData::App(Symbol::Named(name), args),
                FrontendTerm::App(parsed_name, parsed_args),
            ) = (self.ctx.terms.get(term), parsed)
            {
                if name == "and" && parsed_name == "and" && !args.is_empty() {
                    if args.len() != parsed_args.len() {
                        return None;
                    }
                    let args = args.clone();
                    for (index, (&child, parsed_child)) in
                        args.iter().zip(parsed_args).enumerate().rev()
                    {
                        let position = u32::try_from(index).ok()?;
                        let mut child_path = path.clone();
                        child_path.push(position);
                        stack.push((child, parsed_child, child_path));
                    }
                    continue;
                }
            }
            conjuncts.push(Conjunct { path, term, parsed });
        }
        Some(conjuncts)
    }

    /// `(distinct A B)` or `(not (= A B))`, with the parsed operands beside
    /// the raw ones.
    fn disequality_leaf(&self, conjunct: &Conjunct<'_>) -> Option<DisequalityLeaf> {
        let (distinct, parsed_lhs, parsed_rhs) = parsed_disequality(conjunct.parsed)?;
        match self.ctx.terms.get(conjunct.term) {
            TermData::App(Symbol::Named(name), args)
                if distinct && name == "distinct" && args.len() == 2 =>
            {
                Some(DisequalityLeaf {
                    path: conjunct.path.clone(),
                    leaf: conjunct.term,
                    distinct: true,
                    lhs: args[0],
                    rhs: args[1],
                    parsed_lhs: parsed_lhs.clone(),
                    parsed_rhs: parsed_rhs.clone(),
                })
            }
            TermData::Not(inner) if !distinct => {
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(*inner) else {
                    return None;
                };
                if name != "=" || args.len() != 2 {
                    return None;
                }
                Some(DisequalityLeaf {
                    path: conjunct.path.clone(),
                    leaf: conjunct.term,
                    distinct: false,
                    lhs: args[0],
                    rhs: args[1],
                    parsed_lhs: parsed_lhs.clone(),
                    parsed_rhs: parsed_rhs.clone(),
                })
            }
            _ => None,
        }
    }

    /// The fold's own refutation of one authored root through one argument,
    /// or `None` when the argument has no derivation this pass can express.
    fn fold_argument_candidate(
        &mut self,
        root: TermId,
        body: TermId,
        shelled: bool,
        conjuncts: &[Conjunct<'_>],
        argument: &FoldArgument,
    ) -> Option<Proof> {
        let mut candidate = Proof::new();
        let assume = candidate.add_assume(root, None);
        match argument {
            FoldArgument::Identity(path) => {
                let conjunct = conjuncts.iter().find(|conjunct| conjunct.path == *path)?;
                let leaf = self.disequality_leaf(conjunct)?;
                let unit = self.conjunct_unit(&mut candidate, assume, body, shelled, &leaf.path)?;
                if candidate_conclusion(&candidate, unit) != Some(leaf.leaf) {
                    return None;
                }
                self.close_identity(&mut candidate, unit, &leaf)?;
            }
            FoldArgument::Complement { positive, negative } => {
                let positive_conjunct = conjuncts
                    .iter()
                    .find(|conjunct| conjunct.path == *positive)?;
                let negative_conjunct = conjuncts
                    .iter()
                    .find(|conjunct| conjunct.path == *negative)?;
                // The raw negation must be exactly the raw positive under
                // one `not` node: the complement the resolution discharges.
                let literal = positive_conjunct.term;
                if self.ctx.terms.mk_not_raw(literal) != negative_conjunct.term {
                    return None;
                }
                let positive_unit =
                    self.conjunct_unit(&mut candidate, assume, body, shelled, positive)?;
                let negative_unit =
                    self.conjunct_unit(&mut candidate, assume, body, shelled, negative)?;
                // `add_resolution` wants the premise carrying the pivot's
                // NEGATIVE occurrence first.
                candidate.add_resolution(Vec::new(), literal, negative_unit, positive_unit);
            }
            FoldArgument::Propositional => {
                if shelled || root != body {
                    return None;
                }
                propositional::refute_root(&mut self.ctx.terms, &mut candidate, assume, root)?;
            }
        }
        Some(candidate)
    }

    /// Derive the unit `(cl conjunct)` for the conjunct at `path` inside
    /// `body`, from `assume : (cl root)`. With `shelled`, `root` is
    /// `(not (not body))` and the FIRST projection resolves the shelled assume
    /// against `and_pos` on the pivot `(not body)` — the assume carries the
    /// pivot's negation `(not (not body))` — leaving the unit `(cl child)`
    /// exactly as the unshelled chain does; every later level is the ordinary
    /// `and_pos` + resolution pair.
    fn conjunct_unit(
        &mut self,
        candidate: &mut Proof,
        assume: ProofId,
        body: TermId,
        shelled: bool,
        path: &[u32],
    ) -> Option<ProofId> {
        if !shelled {
            let target = conjunct_at(&self.ctx.terms, body, path)?;
            return Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                candidate,
                assume,
                body,
                path,
                target,
            );
        }
        let (&first, rest) = path.split_first()?;
        let child = match self.ctx.terms.get(body) {
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                *args.get(first as usize)?
            }
            _ => return None,
        };
        let not_body = self.ctx.terms.mk_not_raw(body);
        let and_pos = candidate.add_rule_step(
            AletheRule::AndPos(first),
            vec![not_body, child],
            Vec::new(),
            vec![body],
        );
        let unit = candidate.add_resolution(vec![child], not_body, assume, and_pos);
        let target = conjunct_at(&self.ctx.terms, child, rest)?;
        Self::emit_and_pos_chain(&mut self.ctx.terms, candidate, unit, child, rest, target)
    }

    /// Close `(cl leaf)` for an identity leaf: derive `(= A B)`, turn the
    /// leaf into `(cl (not (= A B)))` (`distinct_elim` where the author wrote
    /// `distinct`), and resolve.
    fn close_identity(
        &mut self,
        candidate: &mut Proof,
        unit: ProofId,
        leaf: &DisequalityLeaf,
    ) -> Option<()> {
        let mut budget = MAX_DIFF_NODES;
        let equality = self.derive_normalized_equality(
            candidate,
            leaf.lhs,
            leaf.rhs,
            &leaf.parsed_lhs,
            &leaf.parsed_rhs,
            &mut budget,
        )?;
        let eq = raw_eq(&mut self.ctx.terms, leaf.lhs, leaf.rhs);
        let negated_unit = if leaf.distinct {
            let not_eq = self.ctx.terms.mk_not_raw(eq);
            let elim = raw_eq(&mut self.ctx.terms, leaf.leaf, not_eq);
            let not_elim = self.ctx.terms.mk_not_raw(elim);
            let not_leaf = self.ctx.terms.mk_not_raw(leaf.leaf);
            let distinct_elim = candidate.add_rule_step(
                AletheRule::DistinctElim,
                vec![elim],
                Vec::new(),
                Vec::new(),
            );
            let tautology = candidate.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_elim, not_leaf, not_eq],
                Vec::new(),
                Vec::new(),
            );
            // `add_resolution` wants the premise carrying the pivot's
            // NEGATIVE occurrence first.
            let elided =
                candidate.add_resolution(vec![not_leaf, not_eq], elim, tautology, distinct_elim);
            candidate.add_resolution(vec![not_eq], leaf.leaf, elided, unit)
        } else {
            // The leaf IS `(not (= A B))`; its inner equality must be the
            // very term the derivation concludes.
            let TermData::Not(inner) = self.ctx.terms.get(leaf.leaf) else {
                return None;
            };
            if *inner != eq {
                return None;
            }
            unit
        };
        candidate.add_resolution(Vec::new(), eq, negated_unit, equality);
        Some(())
    }

    /// Derive `(cl (= a b))` for two raw terms that normalize to one canonical
    /// term: `refl` where they are already one term, `cong` over a shared head
    /// with the argument pairs derived recursively, and at an Int-sorted leaf
    /// the Farkas-verified `la_generic` pair joined by `la_disequality`.
    fn derive_normalized_equality(
        &mut self,
        candidate: &mut Proof,
        lhs: TermId,
        rhs: TermId,
        parsed_lhs: &FrontendTerm,
        parsed_rhs: &FrontendTerm,
        budget: &mut usize,
    ) -> Option<ProofId> {
        *budget = budget.checked_sub(1)?;
        if lhs == rhs {
            let eq = raw_eq(&mut self.ctx.terms, lhs, lhs);
            return Some(candidate.add_rule_step(
                AletheRule::Refl,
                vec![eq],
                Vec::new(),
                Vec::new(),
            ));
        }
        let parsed_lhs = strip_frontend_annotations(parsed_lhs);
        let parsed_rhs = strip_frontend_annotations(parsed_rhs);
        // Same head, same arity: congruence over the argument pairs.
        let shared_head = match (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs)) {
            (TermData::App(f, xs), TermData::App(g, ys)) if f == g && xs.len() == ys.len() => {
                Some((xs.clone(), ys.clone()))
            }
            (TermData::Ite(c1, t1, e1), TermData::Ite(c2, t2, e2)) => {
                Some((vec![*c1, *t1, *e1], vec![*c2, *t2, *e2]))
            }
            _ => None,
        };
        if let Some((xs, ys)) = shared_head {
            let (FrontendTerm::App(_, parsed_xs), FrontendTerm::App(_, parsed_ys)) =
                (parsed_lhs, parsed_rhs)
            else {
                return None;
            };
            if parsed_xs.len() != xs.len() || parsed_ys.len() != ys.len() {
                return None;
            }
            let mut premises = Vec::with_capacity(xs.len());
            for index in 0..xs.len() {
                premises.push(self.derive_normalized_equality(
                    candidate,
                    xs[index],
                    ys[index],
                    &parsed_xs[index],
                    &parsed_ys[index],
                    budget,
                )?);
            }
            let eq = raw_eq(&mut self.ctx.terms, lhs, rhs);
            return Some(candidate.add_rule_step(AletheRule::Cong, vec![eq], premises, Vec::new()));
        }
        // An Int-sorted leaf whose two spellings normalize to one linear form:
        // both bounds hold by a unit Farkas combination, and la_disequality
        // turns the pair into the equality.
        if !matches!(self.ctx.terms.sort(lhs), Sort::Int)
            || !matches!(self.ctx.terms.sort(rhs), Sort::Int)
        {
            return None;
        }
        let lhs_canonical = self.ctx.elaborate_surface_subterm(parsed_lhs)?;
        let rhs_canonical = self.ctx.elaborate_surface_subterm(parsed_rhs)?;
        if lhs_canonical != rhs_canonical {
            return None;
        }
        let le_forward = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [lhs, rhs], Sort::Bool);
        let le_reverse = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [rhs, lhs], Sort::Bool);
        let forward = candidate.add_theory_lemma_with_farkas_and_kind(
            "LIA",
            vec![le_forward],
            FarkasAnnotation::from_ints(&[1]),
            TheoryLemmaKind::LiaGeneric,
        );
        let reverse = candidate.add_theory_lemma_with_farkas_and_kind(
            "LIA",
            vec![le_reverse],
            FarkasAnnotation::from_ints(&[1]),
            TheoryLemmaKind::LiaGeneric,
        );
        let eq = raw_eq(&mut self.ctx.terms, lhs, rhs);
        let not_forward = self.ctx.terms.mk_not_raw(le_forward);
        let not_reverse = self.ctx.terms.mk_not_raw(le_reverse);
        let triangle = self.ctx.terms.mk_app(
            Symbol::named("or"),
            [eq, not_forward, not_reverse],
            Sort::Bool,
        );
        let disequality = candidate.add_rule_step(
            AletheRule::LaDisequality,
            vec![triangle],
            Vec::new(),
            Vec::new(),
        );
        let clausified = candidate.add_rule_step(
            AletheRule::Or,
            vec![eq, not_forward, not_reverse],
            vec![disequality],
            Vec::new(),
        );
        let partial =
            candidate.add_resolution(vec![eq, not_reverse], le_forward, clausified, forward);
        Some(candidate.add_resolution(vec![eq], le_reverse, partial, reverse))
    }
}

/// `(= a b)` through the raw application constructor: no orientation, no
/// folding, so the term is exactly what the strict `distinct_elim`, `cong`
/// and `refl` validators decode.
fn raw_eq(terms: &mut ay_core::TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool)
}

/// The single literal a unit step concludes, if it is a unit.
fn candidate_conclusion(candidate: &Proof, step: ProofId) -> Option<TermId> {
    match candidate.steps.get(step.0 as usize)? {
        ay_core::ProofStep::Resolution { clause, .. } | ay_core::ProofStep::Step { clause, .. } => {
            match clause.as_slice() {
                [literal] => Some(*literal),
                _ => None,
            }
        }
        ay_core::ProofStep::Assume(term) => Some(*term),
        _ => None,
    }
}

/// The conjunct reached from `body` along `path` through raw `and` nodes.
fn conjunct_at(terms: &ay_core::TermStore, body: TermId, path: &[u32]) -> Option<TermId> {
    let mut current = body;
    for &position in path {
        current = match terms.get(current) {
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                *args.get(position as usize)?
            }
            _ => return None,
        };
    }
    Some(current)
}

/// `(distinct A B)` or `(not (= A B))` on the parse tree: the operands, and
/// whether the spelling is `distinct`.
fn parsed_disequality(term: &FrontendTerm) -> Option<(bool, &FrontendTerm, &FrontendTerm)> {
    let FrontendTerm::App(name, args) = strip_frontend_annotations(term) else {
        return None;
    };
    if name == "distinct" && args.len() == 2 {
        return Some((true, &args[0], &args[1]));
    }
    if name == "not" && args.len() == 1 {
        if let FrontendTerm::App(inner, inner_args) = strip_frontend_annotations(&args[0]) {
            if inner == "=" && inner_args.len() == 2 {
                return Some((false, &inner_args[0], &inner_args[1]));
            }
        }
    }
    None
}

/// The term under exactly one `(not (not ..))` pair, or the term itself.
fn peel_one_negation_pair(term: &FrontendTerm) -> (&FrontendTerm, bool) {
    if let FrontendTerm::App(outer, outer_args) = term {
        if outer == "not" && outer_args.len() == 1 {
            if let FrontendTerm::App(inner, inner_args) = strip_frontend_annotations(&outer_args[0])
            {
                if inner == "not" && inner_args.len() == 1 {
                    return (strip_frontend_annotations(&inner_args[0]), true);
                }
            }
        }
    }
    (term, false)
}

/// Every conjunct under the `and`-spine of an EXPANDED parsed body, with its
/// child-index path. `None` when the walk exceeds its bound.
fn parsed_conjuncts(term: &FrontendTerm) -> Option<Vec<(Vec<u32>, &FrontendTerm)>> {
    let mut conjuncts = Vec::new();
    let mut stack: Vec<(&FrontendTerm, Vec<u32>)> = vec![(term, Vec::new())];
    let mut visited = 0usize;
    while let Some((term, path)) = stack.pop() {
        visited += 1;
        if visited > MAX_SCANNED_CONJUNCT_NODES {
            return None;
        }
        let term = strip_frontend_annotations(term);
        if let FrontendTerm::App(name, args) = term {
            if name == "and" && !args.is_empty() {
                for (index, child) in args.iter().enumerate().rev() {
                    let position = u32::try_from(index).ok()?;
                    let mut child_path = path.clone();
                    child_path.push(position);
                    stack.push((child, child_path));
                }
                continue;
            }
        }
        conjuncts.push((path, term));
    }
    Some(conjuncts)
}

/// Whether an AUTHORED root — through any `let` levels and one `(not (not
/// ..))` pair, by reference and without expansion — holds a disequality
/// conjunct or a complementary pair of conjuncts under its `and`-spine. A
/// free refusal before any clone or charge. `let`-bound names are compared as
/// the symbols they are, which is exact for a pair written over the same
/// binders and merely conservative otherwise.
fn parsed_root_holds_candidate_conjunct(term: &FrontendTerm) -> bool {
    let mut term = strip_frontend_annotations(term);
    let mut levels = 0usize;
    while let FrontendTerm::Let(_, body) = term {
        levels += 1;
        if levels > MAX_SCANNED_CONJUNCT_NODES {
            return false;
        }
        term = strip_frontend_annotations(body);
    }
    let (term, _) = peel_one_negation_pair(term);
    let mut conjuncts: Vec<&FrontendTerm> = Vec::new();
    let mut stack = vec![term];
    let mut visited = 0usize;
    while let Some(term) = stack.pop() {
        visited += 1;
        if visited > MAX_SCANNED_CONJUNCT_NODES {
            return false;
        }
        let term = strip_frontend_annotations(term);
        if let FrontendTerm::App(name, args) = term {
            if name == "and" {
                stack.extend(args.iter());
                continue;
            }
        }
        if parsed_disequality(term).is_some() {
            return true;
        }
        conjuncts.push(term);
    }
    if conjuncts.len() > MAX_PAIRED_CONJUNCTS {
        return false;
    }
    conjuncts.iter().any(|conjunct| {
        let FrontendTerm::App(name, args) = conjunct else {
            return false;
        };
        name == "not"
            && args.len() == 1
            && conjuncts
                .iter()
                .any(|other| *other == strip_frontend_annotations(&args[0]))
    })
}

/// Whether an AUTHORED root — through any `let` levels — is a candidate for
/// the propositional argument: its Boolean skeleton (`and` / `or` / `not`
/// nodes) reaches `false` in positive or `true` in negative position, or one
/// leaf in both polarities, or a negated direct ITE equality. The latter is
/// only a shape hint: the refuter must find an actual derived guard fact and
/// the unchanged strict checker must validate its intrinsic projection.
/// This scan is by reference, before any clone or source charge.
fn parsed_root_holds_propositional_candidate(term: &FrontendTerm) -> bool {
    use ay_frontend::command::Constant;
    let mut term = strip_frontend_annotations(term);
    let mut levels = 0usize;
    while let FrontendTerm::Let(_, body) = term {
        levels += 1;
        if levels > MAX_SCANNED_CONJUNCT_NODES {
            return false;
        }
        term = strip_frontend_annotations(body);
    }
    let mut positive: Vec<&FrontendTerm> = Vec::new();
    let mut negative: Vec<&FrontendTerm> = Vec::new();
    let mut stack = vec![(term, true)];
    let mut visited = 0usize;
    while let Some((term, polarity)) = stack.pop() {
        visited += 1;
        if visited > MAX_SCANNED_CONJUNCT_NODES {
            return false;
        }
        let term = strip_frontend_annotations(term);
        match term {
            // A constant that refutes where it stands: `false` in positive
            // position, `true` in negative position.
            FrontendTerm::Const(Constant::False) if polarity => return true,
            FrontendTerm::Const(Constant::True) if !polarity => return true,
            FrontendTerm::Const(Constant::True | Constant::False) => {}
            FrontendTerm::App(name, args)
                if (name == "and" || name == "or") && !args.is_empty() =>
            {
                stack.extend(args.iter().map(|arg| (arg, polarity)));
            }
            FrontendTerm::App(name, args) if name == "not" && args.len() == 1 => {
                stack.push((&args[0], !polarity));
            }
            FrontendTerm::App(name, args) if name == "=>" && args.len() == 2 => {
                stack.push((&args[0], !polarity));
                stack.push((&args[1], polarity));
            }
            leaf => {
                // This is only a constant-time candidate shape, not a claim
                // that a branch is selected. The bounded refuter must derive
                // the actual guard and the unchanged checker judges its ITE
                // projection. Do not compare/clone arbitrary leaf subtrees.
                if !polarity
                    && matches!(leaf, FrontendTerm::App(name, args) if name == "=" && args.len() == 2
                        && args.iter().any(|arg| matches!(strip_frontend_annotations(arg), FrontendTerm::App(name, args) if name == "ite" && args.len() == 3)))
                {
                    return true;
                }
                let (same, opposite) = if polarity {
                    (&mut positive, &negative)
                } else {
                    (&mut negative, &positive)
                };
                if opposite.contains(&leaf) {
                    return true;
                }
                if same.len() + opposite.len() >= MAX_PAIRED_CONJUNCTS {
                    return false;
                }
                same.push(leaf);
            }
        }
    }
    false
}

#[path = "authored_fold_identity_propositional.rs"]
mod propositional;

#[path = "authored_fold_raw_spelling.rs"]
mod raw_spelling;

#[cfg(test)]
#[path = "authored_fold_identity_tests.rs"]
mod tests;
