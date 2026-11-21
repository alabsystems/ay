// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Terminal proof-trust and premise-provenance gates.

#[cfg(test)]
mod bv_eq_simplify_tests;
#[cfg(test)]
mod complete_blast_ask_tests;
mod constant_premise;
#[cfg(test)]
mod legacy_subset_kind_tests;
mod native_sos;
#[cfg(test)]
mod nra_sos_tests;
mod screen_declines;
#[cfg(test)]
mod small_linear_wire_tests;

pub(in crate::executor) use screen_declines::WireGapScreenDeclines;

use ay_core::kani_compat::DetHashMap;
use ay_core::{Constant, Proof, ProofStep, Sort, TermData, TermId, TermStore};

use super::super::Executor;

/// Insert `root` and every nested `and`-conjunct beneath it into `set`.
///
/// Top-level `and`-flattening asserts each conjunct of an `(and ...)` problem
/// assertion as a separate `assume`, so the provenance set (leak-2) must
/// accept the conjuncts as well as the asserted conjunction itself. Iterative
/// to avoid deep recursion on wide/nested conjunctions; the `set.insert`
/// visited-guard makes it O(subterms) and cycle-safe.
fn add_term_with_and_conjuncts(
    terms: &TermStore,
    root: TermId,
    set: &mut ay_core::kani_compat::DetHashSet<TermId>,
) {
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !set.insert(term) {
            continue;
        }
        if let TermData::App(sym, args) = terms.get(term) {
            if sym.name() == "and" {
                for &arg in args {
                    stack.push(arg);
                }
            }
        }
    }
}

fn proof_step_clause(proof: &Proof, id: ay_core::ProofId) -> Option<&[TermId]> {
    match proof.steps.get(id.0 as usize)? {
        ProofStep::Assume(term) => Some(std::slice::from_ref(term)),
        ProofStep::Resolution { clause, .. }
        | ProofStep::TheoryLemma { clause, .. }
        | ProofStep::FiniteFieldLinear { clause, .. }
        | ProofStep::NraSos { clause, .. }
        | ProofStep::Step { clause, .. } => Some(clause),
        ProofStep::Anchor { .. } => None,
        _ => None,
    }
}

impl Executor {
    /// Whether one bit-blast theorem is the exact checked wire identity
    /// `x <u 1 <=> x = 0` handled by `format_bv_ult_one_zero_equiv`.
    ///
    /// The printer re-derives this through its bounded pseudo-Boolean template
    /// (at widths through 64), so it is not an honest-hole wire gap.  Keep the
    /// publication screen at least as narrow as that formatter and reject any
    /// surface override on an endpoint the external derivation reads.
    fn bv_ult_one_zero_equivalence_is_fixed_wire(
        &self,
        clause: &[TermId],
        term_overrides: Option<&DetHashMap<TermId, String>>,
    ) -> bool {
        let [equality] = clause else {
            return false;
        };
        let TermData::App(ay_core::Symbol::Named(operator), operands) =
            self.ctx.terms.get(*equality)
        else {
            return false;
        };
        let [left, right] = operands.as_slice() else {
            return false;
        };
        if operator != "=" {
            return false;
        }
        let decode_pair = |ult: TermId, eq_zero: TermId| {
            let TermData::App(ay_core::Symbol::Named(ult_operator), ult_args) =
                self.ctx.terms.get(ult)
            else {
                return None;
            };
            let [subject, one] = ult_args.as_slice() else {
                return None;
            };
            let (subject, one) = (*subject, *one);
            let Sort::BitVec(bits) = self.ctx.terms.sort(subject) else {
                return None;
            };
            let width = bits.width;
            if ult_operator != "bvult" || width == 0 || width > 64 {
                return None;
            }
            let TermData::Const(Constant::BitVec {
                value: one_value,
                width: one_width,
            }) = self.ctx.terms.get(one)
            else {
                return None;
            };
            if *one_width != width || *one_value != 1_u8.into() {
                return None;
            }
            let TermData::App(ay_core::Symbol::Named(eq_operator), eq_args) =
                self.ctx.terms.get(eq_zero)
            else {
                return None;
            };
            let [first, second] = eq_args.as_slice() else {
                return None;
            };
            let is_zero = |term| {
                matches!(
                    self.ctx.terms.get(term),
                    TermData::Const(Constant::BitVec {
                        value: zero_value,
                        width: zero_width,
                    }) if *zero_width == width && *zero_value == 0_u8.into()
                )
            };
            // Equality interning is symmetric and TermId-ordered. Recover the
            // semantic subject/zero roles independently of that storage order.
            let (zero_subject, zero) = if is_zero(*second) {
                (*first, *second)
            } else if is_zero(*first) {
                (*second, *first)
            } else {
                return None;
            };
            let zero_subject_matches = zero_subject == subject
                || matches!(
                    self.ctx.terms.get(zero_subject),
                    TermData::App(ay_core::Symbol::Named(gate), gate_args)
                        if matches!(gate.as_str(), "bvand" | "bvor")
                            && gate_args.as_slice() == [subject, subject]
                            && self.ctx.terms.sort(zero_subject) == self.ctx.terms.sort(subject)
                );
            if eq_operator != "=" || !zero_subject_matches {
                return None;
            }
            Some([ult, eq_zero, subject, one, zero_subject, zero])
        };
        let Some(endpoints) = decode_pair(*left, *right).or_else(|| decode_pair(*right, *left))
        else {
            return false;
        };
        if term_overrides.is_some_and(|overrides| {
            overrides.contains_key(equality)
                || endpoints.iter().any(|term| overrides.contains_key(term))
        }) {
            return false;
        }
        self.recognize_bv_bitblast_until_stopped(clause)
    }

    /// Whether one internally checked bit-blast theorem is also in the exact
    /// ground-constant subset the Alethe printer expands into
    /// `evaluate`/`equiv_pos2`/`false`/`resolution`.
    ///
    /// Keep this deliberately narrower than the printer: a surface override
    /// can change the bytes the external checker sees, so any override on the
    /// accepted shape remains a known gap. Certified authored replacements
    /// purge those overrides before publication. All other `BvBitBlast`
    /// clauses retain the honest `hole` classification.
    fn bv_constant_disequality_is_fixed_wire_evaluate(
        &self,
        clause: &[TermId],
        term_overrides: Option<&DetHashMap<TermId, String>>,
    ) -> bool {
        let [literal] = clause else {
            return false;
        };
        let TermData::Not(equality) = self.ctx.terms.get(*literal) else {
            return false;
        };
        let TermData::App(symbol, operands) = self.ctx.terms.get(*equality) else {
            return false;
        };
        if symbol.name() != "=" || operands.len() != 2 {
            return false;
        }
        let (left, right) = (operands[0], operands[1]);
        let (
            TermData::Const(Constant::BitVec {
                value: left_value,
                width: left_width,
            }),
            TermData::Const(Constant::BitVec {
                value: right_value,
                width: right_width,
            }),
        ) = (self.ctx.terms.get(left), self.ctx.terms.get(right))
        else {
            return false;
        };
        if left_width == &0
            || left_width != right_width
            || left_value == right_value
            || left_value.bits() > u64::from(*left_width)
            || right_value.bits() > u64::from(*right_width)
            || self.ctx.terms.sort(left) != &Sort::bitvec(*left_width)
            || self.ctx.terms.sort(right) != &Sort::bitvec(*right_width)
            || self.ctx.terms.sort(*equality) != &Sort::Bool
            || self.ctx.terms.sort(*literal) != &Sort::Bool
        {
            return false;
        }
        !term_overrides.is_some_and(|overrides| {
            [*literal, *equality, left, right]
                .iter()
                .any(|term| overrides.contains_key(term))
        })
    }

    /// Whether a native Boolean-constant clausification step prints as one of
    /// Alethe's two fixed, premise-free axioms.
    ///
    /// The internal source term in `args` is positional reconstruction
    /// metadata; the printer deliberately omits it.  Any different shape or
    /// surface override stays a known wire gap rather than being inferred safe.
    fn bool_constant_step_is_fixed_wire_axiom(
        &self,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        premises: &[ay_core::ProofId],
        args: &[TermId],
    ) -> bool {
        if !premises.is_empty() || clause.len() != 1 {
            return false;
        }

        let literal = clause[0];
        let source = match rule {
            ay_core::AletheRule::True
                if matches!(
                    self.ctx.terms.get(literal),
                    TermData::Const(Constant::Bool(true))
                ) =>
            {
                literal
            }
            ay_core::AletheRule::False => {
                let TermData::Not(source) = self.ctx.terms.get(literal) else {
                    return false;
                };
                if !matches!(
                    self.ctx.terms.get(*source),
                    TermData::Const(Constant::Bool(false))
                ) {
                    return false;
                }
                *source
            }
            _ => return false,
        };

        if !args.is_empty() && args != [source] {
            return false;
        }
        !self
            .last_proof_term_overrides
            .as_ref()
            .is_some_and(|overrides| {
                overrides.contains_key(&literal) || overrides.contains_key(&source)
            })
    }

    /// Internal proof retained for terminal publication policy.
    ///
    /// Unlike [`Self::last_proof`], this deliberately does not require a
    /// user-facing artifact request: mandatory proof tracking also serves
    /// `:check-proofs-strict` when that option is enabled by itself. Explicit
    /// reconstruction suppression still hides the proof, and ordinary query
    /// invalidation clears the underlying slot before a later policy check.
    fn retained_unsat_proof_for_policy(&self) -> Option<&Proof> {
        if self.last_unsat_proof_reconstruction_suppressed {
            None
        } else {
            self.last_proof.as_ref()
        }
    }

    /// Build the set of `assume` terms an external checker may legitimately
    /// accept as free hypotheses for the last UNSAT proof (leak-2 provenance
    /// gate).
    ///
    /// A terminal-path `assume` is trustworthy ONLY when its term is one of:
    ///   (A) an original asserted formula — the parsed-prefix problem premises
    ///       and any provenance-tracked problem assertions (never the full
    ///       solver-time assertion stack, which may hold theory-injected
    ///       axioms) — plus their nested `and`-conjuncts (top-level
    ///       and-flattening asserts each conjunct as a separate `assume`) plus
    ///       any `check-sat-assuming` assumption literals; or
    ///   (B) a quantifier instantiation whose `QuantExpansionRecord.original`
    ///       traces back to an asserted `forall` in (A): the `forall` itself,
    ///       the merged ground `expanded` conjunction that replaced it, and
    ///       each per-instance folded term.
    ///
    /// Any reachable terminal `assume` OUTSIDE this set is a laundered axiom —
    /// the theory asserted a fact it never proved (e.g. an injected `seq.len`
    /// identity) and rode it to a "certified" empty clause. The strict-proofs
    /// and `--self-check` gates treat such an `assume` exactly like a `trust`
    /// fallback and downgrade the verdict to `unknown`.
    pub(in crate::executor) fn proof_legit_assume_set(
        &self,
    ) -> ay_core::kani_compat::DetHashSet<TermId> {
        let mut set: ay_core::kani_compat::DetHashSet<TermId> =
            ay_core::kani_compat::DetHashSet::default();

        // (A) Original problem premises + their nested and-conjuncts.
        for assertion in self.proof_original_problem_assertions() {
            add_term_with_and_conjuncts(&self.ctx.terms, assertion, &mut set);
        }
        for assertion in self.proof_problem_assertions() {
            add_term_with_and_conjuncts(&self.ctx.terms, assertion, &mut set);
        }
        // check-sat-assuming assumption literals are problem-supplied premises.
        if let Some(assumptions) = &self.last_assumptions {
            for &assumption in assumptions {
                add_term_with_and_conjuncts(&self.ctx.terms, assumption, &mut set);
            }
        }
        // Re-elaborated original terms captured by the proof rebuild. The
        // trust surgery inserts `assume` steps carrying these (alpha-renamed
        // `forall` premises have a canonical id distinct from `ctx.assertions`
        // — see `last_proof_rebuild_originals`), so they must count as (A).
        for &original in &self.last_proof_rebuild_originals {
            add_term_with_and_conjuncts(&self.ctx.terms, original, &mut set);
        }

        // (B) Quantifier instantiations rooted at an asserted `forall`.
        //
        // `expand_finite_domains` REPLACES a top-level asserted `forall` at
        // `ctx.assertions[idx]` with its ground expansion in place, so the
        // `forall` itself is no longer in (A) (that slot now holds `expanded`).
        // Each `QuantExpansionRecord` is created ONLY for such a replacement of
        // a top-level `forall` premise (see `expand_finite_domains`), so
        // `rec.original` IS a genuinely-asserted premise — accept it, plus the
        // ground `expanded` conjunction that replaced it and each per-instance
        // folded term (the terms a `forall_inst` derivation legitimately
        // introduces). The `TermData::Forall` guard re-checks the construction
        // invariant (an injected non-forall axiom never gets a record and so
        // never launders through here).
        for rec in &self.quant_expansion_records {
            if !matches!(self.ctx.terms.get(rec.original), TermData::Forall(..)) {
                continue;
            }
            add_term_with_and_conjuncts(&self.ctx.terms, rec.original, &mut set);
            // (#bv-forall-const-expansion) A record whose expansion collapsed to
            // a CONSTANT contributes no premise: whitelisting `true`/`false` here
            // would widen the foreign-assume detector's accept set for a term
            // that is not a problem premise at all. Records for such expansions
            // exist only to authenticate the replacement for the BV full-domain
            // SAT recognizer (see `expand_finite_domains`), so this keeps the
            // proof-provenance surface byte-identical to before that change.
            if !matches!(self.ctx.terms.get(rec.expanded), TermData::Const(_)) {
                add_term_with_and_conjuncts(&self.ctx.terms, rec.expanded, &mut set);
            }
            for (_binder_values, folded) in &rec.instances {
                add_term_with_and_conjuncts(&self.ctx.terms, *folded, &mut set);
            }
        }

        // #rewritten-constant-premise: authenticate constants only after every
        // provenance source has contributed to the finished set. See the
        // `constant_premise` module for rationale and incident evidence.
        let (authored_true, authored_false) = self.boolean_constant_premises_authored();
        if !authored_true {
            set.remove(&self.ctx.terms.true_term());
        }
        if !authored_false {
            set.remove(&self.ctx.terms.false_term());
        }

        set
    }

    /// Whether the last UNSAT proof has a reachable terminal `assume` NOT
    /// backed by the problem's provenance (leak-2). Consulted by both the
    /// `--strict-proofs` CLI gate and the `--self-check` self-certification
    /// gate; a `true` result downgrades the UNSAT to a sound `unknown`.
    ///
    /// The provenance set is keyed by `TermId`, and that is not sufficient on
    /// its own — a `TermId` records what AY STORES, and `TermStore::mk_not`
    /// eliminates a double negation at construction, so `(assert (not (not
    /// phi)))` puts `phi` in the provenance set and an `assume phi` reads as
    /// backed. The document is still a proof of something the problem does not
    /// state, and carcara refuses it at that first leaf. The second arm asks
    /// the question the first cannot: is there an authored SPELLING for this
    /// leaf that the printer can put in the document?
    #[must_use]
    pub fn unsat_proof_terminal_foreign_assume(&self) -> bool {
        let Some(proof) = self.retained_unsat_proof_for_policy() else {
            return false;
        };
        let legit: ay_core::kani_compat::DetHashSet<TermId> =
            self.finite_enum_scope_for_proof(proof).map_or_else(
                || self.proof_legit_assume_set(),
                |scope| scope.into_iter().collect(),
            );
        if ay_proof::terminal_trust_report_with_provenance(proof, |t| legit.contains(&t))
            .foreign_assume_on_path
            > 0
        {
            return true;
        }
        let unspellable = self.unbridgeable_authored_assume_terms();
        if unspellable.is_empty() {
            return false;
        }
        ay_proof::terminal_trust_report_with_provenance(proof, |t| !unspellable.contains(&t))
            .foreign_assume_on_path
            > 0
    }

    /// The PARSE verdict the `--strict-proofs` and `--self-check` gates refuse
    /// on: the last UNSAT proof and its problem scanned with the source-syntax
    /// override table (`last_proof_term_overrides`), without rendering.
    ///
    /// Read on the same proof and override table those gates consult, so the
    /// CLI's disclosure and the refusal can never disagree. `None` when no
    /// UNSAT proof is retained.
    ///
    /// Only ever `Supported` or `Unsupported`: what a render prints — a
    /// spelling only Clean's vendored Carcara checks, a `:rule let` over the
    /// problem's own `let` — is unknown until it renders, and those gates
    /// admit such a document (external-codegen promotes on Clean under
    /// `--strict-proofs`). So its `Supported` is not a verdict on any
    /// document, and it is not public: it read `Supported` for the UMULL
    /// `zero_extend` twin whose document pinned Carcara 9a352ee refuses.
    /// Public readers say what a render printed:
    /// [`Self::last_unsat_proof_carcara_surface`] renders, and
    /// [`Self::try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface`]
    /// folds in the report of the render that streamed the CLI's certificate.
    pub(crate) fn strict_gate_carcara_surface(&self) -> Option<ay_proof::CarcaraSurface> {
        let proof = self.retained_unsat_proof_for_policy()?;
        if let Some(support) = self.checked_external_proof_support_for_current_proof() {
            return Some(support.surface().clone());
        }
        Some(self.problem_and_proof_surface(proof, self.last_proof_term_overrides.as_ref()))
    }

    /// Whether the last UNSAT proof references syntax the pinned Carcara
    /// checker cannot parse losslessly.
    ///
    /// `Seq`, `FloatingPoint`, and `Char` sorts are not in that checker's sort
    /// grammar. In addition, SMT-LIB symbols containing `|` or `\` have no
    /// lossless standard quoted spelling accepted by Carcara (AY/Z3's escape
    /// extension is rejected). Such a proof is NOT independently checkable
    /// and carries no separate certificate. AY can still find a
    /// sound *internal* refutation — e.g. a `(seq.nth s 0)` term forced to two
    /// distinct integer constants collapses to a clean `la_generic` +
    /// `resolution` chain with zero `hole`/`trust` steps and no foreign
    /// `assume` — so neither the trust/hole gate nor the leak-2 provenance gate
    /// fires, and the UNSAT would ship *bare* under `--strict-proofs` with no
    /// checker able to confirm it. That is a §0-class certification leak: a
    /// strict gate that promises "only results AY can independently verify"
    /// must downgrade this to a sound `unknown`. Consulted by the
    /// `--strict-proofs` CLI gate and the `--self-check` self-certification
    /// gate alongside [`Self::unsat_proof_terminal_foreign_assume`].
    ///
    /// This is the strict gates' parse verdict as a predicate: `false` is not
    /// a claim that pinned Carcara checks the rendered document (a Clean-only
    /// spelling, which these gates admit, is no reason here; read
    /// [`Self::last_unsat_proof_carcara_surface`] for the document). It gates
    /// only the consumers that claim an external check; the document itself
    /// renders and is exported with the surface disclosed (D7).
    #[must_use]
    pub fn unsat_proof_references_uncheckable_seq_theory(&self) -> bool {
        self.strict_gate_carcara_surface()
            .is_some_and(|surface| !surface.is_supported())
    }

    /// Why the strict-proof gate refuses the last UNSAT: every arm of
    /// [`Self::unsat_proof_terminal_trust_detected`] that fires, named — for
    /// the `unknown.detail` record beside `UnknownReason::ProofTrusted`, so
    /// the refusal a claiming consumer publishes carries its reason (D7).
    ///
    /// Must be read BEFORE the unknown is published: publication revokes the
    /// proof every arm reads.
    #[must_use]
    pub(crate) fn terminal_trust_refusal_detail(&self) -> String {
        let mut causes = Vec::new();
        if self
            .retained_unsat_proof_for_policy()
            .is_some_and(|proof| ay_proof::terminal_trust_report(proof).has_terminal_trust())
        {
            causes.push("a trust or hole step reaches the empty clause".to_string());
        }
        if self.unsat_proof_terminal_foreign_assume() {
            causes.push("an assume on the empty-clause path is not a problem premise".to_string());
        }
        if let Some(reason) = self
            .strict_gate_carcara_surface()
            .and_then(|surface| surface.unsupported_reason().map(str::to_string))
        {
            causes.push(format!(
                "the certificate's external-recheck surface is unsupported: {reason}"
            ));
        }
        if causes.is_empty() {
            causes.push("the terminal derivation chain is not trust-free".to_string());
        }
        format!(
            "strict proofs withheld a computed UNSAT because {}",
            causes.join("; ")
        )
    }

    /// Whether the last UNSAT proof's terminal derivation chain is NOT
    /// trust-free — the deciding predicate of the #8759 strict-proof gate.
    ///
    /// Three independent ways an `unsat` can reach the empty clause without an
    /// end-to-end checkable derivation, any one of which disqualifies it:
    ///
    /// * a `:rule trust`/`hole` step or trust-kind theory lemma is reachable
    ///   from the empty clause;
    /// * an `assume` leaf on that path is not backed by the problem's
    ///   provenance ([`Self::unsat_proof_terminal_foreign_assume`], leak-2) — a
    ///   laundered free axiom is exactly as unverified as a `trust` step;
    /// * the proof references sequence-theory content no external checker can
    ///   parse ([`Self::unsat_proof_references_uncheckable_seq_theory`]).
    ///
    /// This is the ONE definition. It used to live in the `ay` binary
    /// (`crates/ay/src/run.rs::terminal_trust_detected`), which meant a library
    /// consumer of `ay-dpll` got no gate at all: on a clean-but-uncheckable
    /// `Seq` refutation the CLI printed `unknown (incomplete proof-trusted)`
    /// while the same solver returned `unsat` through `Solver::check_sat`. The
    /// CLI now delegates here, and `certify_unsat_for_publication` — the single
    /// public UNSAT funnel — enforces it on every public UNSAT, so both
    /// boundaries answer identically.
    #[must_use]
    pub fn unsat_proof_terminal_trust_detected(&self) -> bool {
        self.retained_unsat_proof_for_policy()
            .is_some_and(|proof| ay_proof::terminal_trust_report(proof).has_terminal_trust())
            || self.unsat_proof_terminal_foreign_assume()
            || self.unsat_proof_references_uncheckable_seq_theory()
    }

    /// Conservative screen for native steps whose effective Alethe spelling
    /// is known to require an honest unproved fallback.
    ///
    /// This is deliberately deny-only. It scans every stored step because the
    /// exporter emits the whole proof, not just the terminal cone, but it does
    /// not attempt to predict every clause-sensitive printer rewrite. The one
    /// evidence-sensitive exception is `LiaGeneric`, whose complete-step
    /// decision is shared with the printer. A known wire gap is sufficient to
    /// refuse `:check-proofs-strict`; absence of one is not advertised as
    /// external semantic validation.
    #[must_use]
    pub fn unsat_proof_has_known_wire_gap(&self) -> bool {
        let Some(proof) = self.retained_unsat_proof_for_policy() else {
            return false;
        };
        self.proof_has_known_wire_gap(proof)
    }

    /// Apply the wire-gap screen to a proof that has not yet been published
    /// into `last_proof`. Proof construction uses this so it never has to
    /// overwrite retained query state merely to inspect a candidate.
    ///
    /// One publication asks this about the SAME finished document several
    /// times — `authored_cascade_publishable`'s entry guard,
    /// `retry_native_strict_wire_gap`'s guard plus its three inter-repair
    /// re-asks, the post-fallback ask in
    /// `apply_authored_replacements_and_derivations`, and the public policy
    /// entries in `unsat_cert`. Each ask re-runs the screen in full, because
    /// the document can change between them and a stale ADMIT would let
    /// timing decide publication.
    ///
    /// What each ask must NOT re-run is the bit-blast refutation underneath
    /// it. `ay_proof::checked_bv_bitblast_lowering_supported` answers a
    /// SUPPORT question by building the answer and discarding it, and the
    /// exporter then builds the same documents again to keep their text. That
    /// duplication is removed where it happens, at the refutation:
    /// `ay_proof::resolution_dag_memo` keys a completed refutation on the CNF
    /// that it refutes, so each distinct bit-blast is solved once however many
    /// times this screen runs. Measured on an 8-bit wraparound publication,
    /// one lemma was refuted six times; it is now refuted once.
    ///
    /// The complete bit-blast, which answers by building the whole answer, is
    /// asked only while a document is observable (`proof_document_observable`),
    /// and then only until the stop proof assembly observes
    /// (`make_proof_assembly_should_stop`: the interrupt, the certification
    /// deadline). Otherwise a lemma only it could lower is a gap. Across
    /// decisions a refused answer is never memoized, but for the monolithic
    /// refutation's counted envelope (`complete_blast/transport/monolithic.rs`):
    /// 470d83f28 let the lane take the positive unit `(= L R)` of an elaborated
    /// 64-bit affine identity, and with no proofs requested this screen then
    /// ran for over 50 minutes on `bv_affine_source`'s constant multiples,
    /// which certify from the strict checker alone; under a bare self-check
    /// with a 20 s timeout it ran past 100 s. Within one public decision, a
    /// question declined unstopped is not asked again
    /// (`terminal_trust/screen_declines.rs`): under `:check-proofs-strict` with
    /// no timeout the same identity was asked 14 times in one decision, each
    /// ask repaying the sweep's 120 s wall.
    pub(in crate::executor) fn proof_has_known_wire_gap(&self, proof: &Proof) -> bool {
        // Preflight before either expensive arithmetic recognizer: an
        // over-cap proof receives ZERO general promotion attempts. Continue
        // screening through the shared predicate, which can directly decide
        // fully inspected small linear BV identities without a general probe.
        // Large/opaque arithmetic still declines before any surface walk or
        // general recognizer, as in the printer.
        let mut poly_simp_budget = ay_proof::ArithPolySimpPromotionBudget::for_proof(proof);
        if !poly_simp_budget.proof_admitted()
            && proof.steps.iter().any(|step| match step {
                ProofStep::TheoryLemma {
                    kind, lia, clause, ..
                } if matches!(kind, ay_core::TheoryLemmaKind::ArithClauseTautology)
                    || (matches!(kind, ay_core::TheoryLemmaKind::LiaGeneric)
                        && matches!(lia, Some(ay_core::LiaAnnotation::LinearIdentity))) =>
                {
                    // The over-cap budget has zero general attempts. Only
                    // the direct bounded decision can succeed here. Actual
                    // source overrides are still checked by the full scan.
                    !ay_proof::theory_lemma_poly_simp_lowering_supported(
                        &self.ctx.terms,
                        kind,
                        lia.as_ref(),
                        clause,
                        None,
                        &mut poly_simp_budget,
                    )
                }
                _ => false,
            })
        {
            return true;
        }
        // This is the same effective source-syntax channel handed to the
        // ordinary Alethe exporter. In particular, a `LiaGeneric` Farkas
        // certificate may not gain `la_generic` authority from the internal
        // term DAG while the printer is rendering different text.
        let raw_term_overrides = self.proof_export_term_overrides();
        if !ay_proof::carcara_proof_surface_is_supported(
            proof,
            &self.ctx.terms,
            raw_term_overrides.as_ref(),
        ) {
            return true;
        }
        let term_overrides = match self
            .effective_wire_term_overrides_for_export(proof, raw_term_overrides.as_ref())
        {
            Ok(overrides) => overrides,
            // The exporter runs this same bounded authored-assume planner.
            // If it cannot prove and confine a source spelling, downstream
            // wire compatibility is unknown and publication must fail closed.
            Err(_) => return true,
        };
        // Shared by every shadowed-store render in this proof, including
        // failed attempts, so many individually bounded lemmas cannot multiply
        // the publication screen's allowance.
        let mut shadowed_store_work = 64 * 1024 * 1024;
        let mut ground_substitution_work = 8 * 1024 * 1024;
        let mut guarded_row_work = 8 * 1024 * 1024;
        let mut negated_exists_work = 8 * 1024 * 1024;
        let mut arith_chain_work = 8 * 1024 * 1024;
        let stop = self.make_proof_assembly_should_stop();
        let complete_blast = self
            .proof_document_observable()
            .then_some(&stop as &dyn Fn() -> bool);
        proof.steps.iter().any(|step| match step {
            ProofStep::Assume(term) => {
                let surface = term_overrides
                    .as_ref()
                    .and_then(|overrides| overrides.get(term));
                match surface {
                    Some(surface) if surface.starts_with("(let") => {
                        !ay_proof::certified_let_assume_bridge_is_supported(
                            &self.ctx.terms,
                            *term,
                            surface,
                            term_overrides.as_ref(),
                        )
                    }
                    _ => matches!(self.ctx.terms.get(*term), TermData::Let(..)),
                }
            }
            ProofStep::TheoryLemma {
                clause,
                farkas,
                kind,
                lia,
                ..
            } => {
                if matches!(kind, ay_core::TheoryLemmaKind::BvUremBound) {
                    return !self.urem_bound_wire_supported(clause, term_overrides.as_ref());
                }
                if matches!(kind, ay_core::TheoryLemmaKind::GroundEqualitySubstitution)
                    && ay_proof::checked_ground_substitution_lowering_supported(
                        &self.ctx.terms,
                        clause,
                        term_overrides.as_ref(),
                        &mut ground_substitution_work,
                    )
                {
                    return false;
                }
                if matches!(kind, ay_core::TheoryLemmaKind::BvMulOverflowDivision)
                    && ay_proof::mul_overflow_division_lowering_supported(
                        &self.ctx.terms,
                        clause,
                        term_overrides.as_ref(),
                    )
                {
                    return false;
                }
                if matches!(kind, ay_core::TheoryLemmaKind::ArraySelectStore { .. } | ay_core::TheoryLemmaKind::ArrayRowChain)
                    && ay_proof::checked_array_read_lowering_supported(
                        &self.ctx.terms,
                        kind,
                        clause,
                        term_overrides.as_ref(),
                        &mut guarded_row_work,
                    )
                {
                    return false;
                }
                if matches!(kind, ay_core::TheoryLemmaKind::ArrayRowChain)
                    && ay_proof::checked_shadowed_stores_lowering_supported(
                        &self.ctx.terms,
                        clause,
                        term_overrides.as_ref(),
                        &mut shadowed_store_work,
                    )
                {
                    return false;
                }
                if matches!(kind, ay_core::TheoryLemmaKind::IteBranchProjection)
                    && ay_proof::checked_ite_branch_projection_lowering_supported(
                        &self.ctx.terms,
                        clause,
                        term_overrides.as_ref(),
                        &mut guarded_row_work,
                    )
                {
                    return false;
                }
                if matches!(kind, ay_core::TheoryLemmaKind::ArrayGuardedRowExpansion)
                    && ay_proof::checked_guarded_row_expansion_lowering_supported(
                        &self.ctx.terms,
                        clause,
                        term_overrides.as_ref(),
                        &mut guarded_row_work,
                    )
                {
                    return false;
                }
                let checked_bv_lowering = self.screen_bv_bitblast_supported(
                    kind,
                    clause,
                    term_overrides.as_ref(),
                    complete_blast,
                );
                // These legacy shapes describe the bit-blast printer arm.
                // Other lemma kinds can carry the same clause but must still
                // pass their own unchanged wire rule below. Compare the same
                // effective source spellings the shared printer just read.
                debug_assert!(
                    !matches!(
                        kind,
                        ay_core::TheoryLemmaKind::BvBitBlast
                            | ay_core::TheoryLemmaKind::BvBitBlastGate { .. }
                    ) || (!self.bv_constant_disequality_is_fixed_wire_evaluate(
                        clause,
                        term_overrides.as_ref(),
                    ) && !self.bv_ult_one_zero_equivalence_is_fixed_wire(
                        clause,
                        term_overrides.as_ref(),
                    ))
                        || checked_bv_lowering,
                    "legacy exact BV subsets must stay inside shared printer admission: kind={kind:?}, clause={clause:?}"
                );
                if checked_bv_lowering {
                    return false;
                }
                if matches!(
                    kind,
                    ay_core::TheoryLemmaKind::ArithClauseTautology
                        | ay_core::TheoryLemmaKind::LiaGeneric
                ) && ay_proof::theory_lemma_poly_simp_lowering_supported(
                    &self.ctx.terms,
                    kind,
                    lia.as_ref(),
                    clause,
                    term_overrides.as_ref(),
                    &mut poly_simp_budget,
                ) {
                    return false;
                }
                if self.screen_bv_arithmetic_supported(
                    kind,
                    clause,
                    term_overrides.as_ref(),
                    &mut poly_simp_budget,
                    complete_blast,
                ) {
                    return false;
                }
                // Where the printer asks it: after both proof-wide `poly_simp`
                // spenders above, and never for a Farkas-annotated lemma (the
                // printer ships those through its Farkas lane, as `hole`).
                if matches!(kind, ay_core::TheoryLemmaKind::ArithClauseTautology)
                    && farkas.is_none()
                    && ay_proof::arith_equality_chain_lowering_supported(
                        &self.ctx.terms,
                        clause,
                        term_overrides.as_ref(),
                        &mut arith_chain_work,
                    )
                {
                    return false;
                }
                if matches!(kind, ay_core::TheoryLemmaKind::ArithClauseTautology)
                    && farkas.is_none()
                    && ay_proof::arith_order_split_lowering(
                        &self.ctx.terms, clause, term_overrides.as_ref(),
                    ).is_some()
                {
                    return false;
                }
                if matches!(kind, ay_core::TheoryLemmaKind::ArithEqTriangle)
                    && ay_proof::arith_eq_triangle_lowering_supported(
                        &self.ctx.terms,
                        clause,
                        term_overrides.as_ref(),
                    )
                {
                    return false;
                }
                if ay_proof::arith_disequality_split_lowering_supported(
                    &self.ctx.terms,
                    kind,
                    clause,
                    term_overrides.as_ref(),
                ) {
                    return false;
                }
                if ay_proof::arith_proportional_equality_lowering_supported(
                    &self.ctx.terms,
                    kind,
                    clause,
                    term_overrides.as_ref(),
                ) {
                    return false;
                }
                if ay_proof::checked_unary_congruence_lowering_supported(
                    &self.ctx.terms,
                    kind,
                    clause,
                    term_overrides.as_ref(),
                ) {
                    return false;
                }
                if ay_proof::checked_lia_equality_chain_lowering_supported(
                    &self.ctx.terms,
                    kind,
                    clause,
                    term_overrides.as_ref(),
                    &mut arith_chain_work,
                ) {
                    return false;
                }
                if ay_proof::checked_affine_equality_cycle_lowering_supported(
                    &self.ctx.terms,
                    kind,
                    clause,
                    term_overrides.as_ref(),
                    &mut arith_chain_work,
                ) {
                    return false;
                }
                if matches!(kind, ay_core::TheoryLemmaKind::ArithEqImpliesBound)
                    && ay_proof::arith_eq_implies_bound_lowering_supported(
                        &self.ctx.terms,
                        clause,
                        term_overrides.as_ref(),
                    )
                {
                    return false;
                }
                if matches!(kind, ay_core::TheoryLemmaKind::IntBoundsTautology)
                    && ay_proof::int_bounds_tautology_lowering_supported(
                        &self.ctx.terms,
                        clause,
                        term_overrides.as_ref(),
                    )
                {
                    return false;
                }
                if ay_proof::lia_lattice_lowering_supported(
                    &self.ctx.terms,
                    step,
                    term_overrides.as_ref(),
                ) {
                    return false;
                }
                // The kind's wire rule is `hole` in every dialect; only the
                // Clean dialect's render prints it as Clean's `dt_project`,
                // so the screen asks the lowering in this executor's dialect.
                if matches!(kind, ay_core::TheoryLemmaKind::DatatypeSelectorProject)
                    && ay_proof::dt_project_lowering_supported(
                        self.alethe_dialect(),
                        &self.ctx.terms,
                        clause,
                        term_overrides.as_ref(),
                    )
                {
                    return false;
                }
                if matches!(kind, ay_core::TheoryLemmaKind::EufTransitive) {
                    return !ay_proof::checked_euf_transitive_lowering_supported(
                        &self.ctx.terms,
                        clause,
                        term_overrides.as_ref(),
                        &mut arith_chain_work,
                    );
                }
                let wire = ay_proof::promoted_wire_rule(
                    &self.ctx.terms,
                    kind,
                    clause,
                    farkas.as_ref(),
                    term_overrides.as_ref(),
                );
                wire == ay_core::UNPROVED_STEP_RULE
                    || ay_core::alethe_rule_requires_premises_or_args(wire)
            }
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => {
                if matches!(rule, ay_core::AletheRule::QntNegExists) {
                    return !premises.is_empty()
                        || !args.is_empty()
                        || !ay_proof::qnt_neg_exists_step_lowering_supported(
                            &self.ctx.terms,
                            clause,
                            term_overrides.as_ref(),
                            &mut negated_exists_work,
                        );
                }
                if matches!(rule, ay_core::AletheRule::BvReconstructV1) {
                    return !ay_proof::bv_reconstruct_step_lowering_supported(
                        self.alethe_dialect(),
                        &self.ctx.terms,
                        clause,
                        premises.len(),
                        args.len(),
                        term_overrides.as_ref(),
                    );
                }
                if matches!(rule, ay_core::AletheRule::BvOffsetSpinesV1) {
                    return !ay_proof::bv_offset_spines_step_lowering_supported(
                        self.alethe_dialect(),
                        &self.ctx.terms,
                        clause,
                        premises.len(),
                        args.len(),
                        term_overrides.as_ref(),
                    );
                }
                if matches!(rule, ay_core::AletheRule::EqSimplify) {
                    return !ay_proof::bv_eq_simplify_step_lowering_supported(
                        self.alethe_dialect(),
                        &self.ctx.terms,
                        clause,
                        premises.len(),
                        args.len(),
                        term_overrides.as_ref(),
                    );
                }
                let trans_surface_gap = matches!(rule, ay_core::AletheRule::Trans)
                    && premises
                        .iter()
                        .map(|premise| proof_step_clause(proof, *premise))
                        .collect::<Option<Vec<_>>>()
                        .is_none_or(|premise_clauses| {
                            !ay_proof::trans_step_surface_is_supported(
                                &self.ctx.terms,
                                clause,
                                &premise_clauses,
                                term_overrides.as_ref(),
                            )
                        });
                (matches!(rule, ay_core::AletheRule::True | ay_core::AletheRule::False)
                    && !self.bool_constant_step_is_fixed_wire_axiom(rule, clause, premises, args))
                    || (matches!(rule, ay_core::AletheRule::Evaluate)
                        && !ay_proof::evaluate_step_lowering_supported(
                            &self.ctx.terms,
                            clause,
                            term_overrides.as_ref(),
                        ))
                    || trans_surface_gap
                    || rule.wire_name() == ay_core::UNPROVED_STEP_RULE
            }
            // Native SOS acceptance alone never authorizes publication: only a
            // step the printer's checked lowering renders has no wire gap.
            step @ ProofStep::NraSos { .. } => self.sos_wire_gap(step, term_overrides.as_ref()),
            ProofStep::Resolution { .. } | ProofStep::Anchor { .. } => false,
            _ => true,
        })
    }
}
