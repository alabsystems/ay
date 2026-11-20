// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Attributed reasons for declining to record a proof at all.
//!
//! A refutation that ships `(step t0 (cl) :rule hole)` — one line, no
//! premises, no derivation — says only "AY refuted this and kept nothing".
//! Two entirely different machines produce that artifact
//! (`install_uncertifiable_proof_poison` and `false_source`'s
//! `set_empty_hole`), and inside the first one at least three distinct
//! conditions reach it. A corpus census over the emitted artifacts therefore
//! reported ONE bucket ("step t0 uses unverified trust rule", 44 instances of
//! the measured 68) for causes whose remedies have nothing in common.
//!
//! Measured on the QF_DT `barrett-jsat/typed` family at 800b0668e, with the
//! `--proof` verdict lost on every one of them:
//!
//! | instance          | nodes in the single authored root | mechanism |
//! |-------------------|-----------------------------------|-----------|
//! | `typed_v1l80035`  | 11,054                            | root unbounded |
//! | `typed_v1l60098`  | 128,309                           | root unbounded |
//! | `typed_v2l20006`  | 48                                | fold-to-`false` |
//! | `typed_v1l20003`  | 75                                | fold-to-`false` |
//!
//! The first class was refused by a per-root RENDERING bound
//! (`MAX_SURFACE_NODES`, 8,192 nodes/root) before any proof machinery ran;
//! the second class has a bounded source, reaches a real proof, and then has
//! that proof erased because it rests on an `assume false` the preprocessor
//! manufactured. Naming them apart is the whole point: the first wants a
//! rendering budget that reflects real work, the second wants the
//! preprocessor's own argument recorded (see `authored_conjunct_eval`).
//! Since 2026-09-29 the gate prices the build pass as the single traversal it
//! is (`SurfaceWorkModel::Traversal`); the per-subtree bound stays with the
//! renderers that need it, each at its own site.
//!
//! This is deliberately NOT a weakening of any gate. The decline still
//! happens, the artifact is still fail-closed, and the verdict still
//! downgrades. Only the LABEL changes, from anonymous to attributed.
//!
//! # Widened at #evidence-stage-3, and why the tag space is one enum
//!
//! The first four mechanisms cover the two poisons above. They attributed 12
//! of 101 published `unsat` verdicts on a 629-file corpus census; the other 89
//! said nothing at all — 46 emitting no certificate, 32 emitting a holey one.
//! An evidence class that cannot be named cannot be ranked, and the campaign
//! had already spent effort on five hypotheses a later measurement killed.
//!
//! So this enum now spans the whole distance between "AY refuted this" and
//! "…and here is externally checkable evidence", not just the two poisons:
//!
//! * **assembly** — a producer declined, or a pass poisoned the proof
//!   (`AuthoredSource*`, `PreprocessorFoldToFalse*`,
//!   `AuthoredSurfaceOverridePlanUnbounded`, `InputSyntaxRewriteSourceBudget`);
//! * **publication lane** — an independent authority admitted the verdict and
//!   the derivation was never rendered or was deleted
//!   (`CheckedSemanticCertificateUnrendered`, `QuantifierArtifactFirewall`);
//! * **closure** — the refutation was closed by a trust head rather than
//!   derived (`AssumeFamilyTrustClosure`, `DerivedLeafTrustClosure`);
//! * **document** — a derivation exists and the artifact still is not evidence
//!   (`TerminalTrustStepOnPath`, `PrinterRuleWithoutExternalSpelling`);
//! * **presentation** — the derivation survives and its AUTHORED-SCOPE
//!   spelling does not (`NonPortableGroundEvaluate`,
//!   `AuthoredAssumeSurfaceUnavailable`, `AuthoredSourceAuthorityInvalid`,
//!   `RetentionOffWithoutAuthoredText`, `ForallInstanceSurfaceConflict`);
//! * **render/write** — the artifact was refused after the mint
//!   (`AletheEmissionWorkBudget`, `UndeclarableProofSymbols`,
//!   `PinnedCheckerSurfaceUnsupported`, `ProofSurfaceBridgeMissing`,
//!   `StaleAuthenticatedExportScope`, `CertificateWriteFailed`).
//!
//! One enum, because a census buckets on ONE tag space and the whole point of
//! the exercise is that the buckets be comparable. `NoDerivationRecorded` is
//! the residual: it is a bug report saying a silent site is still out there,
//! and it should trend to zero.
//!
//! The CLI reports exactly one of these per unevidenced verdict, and the
//! precedence is deliberate: a mechanism recorded during ASSEMBLY outranks one
//! derived from the render, because the render is merely the first gate to
//! fire. That ordering is what stops the floating-point family — which has no
//! derivation at all — from being filed under a printing limitation.

/// Why the last UNSAT refutation carries no externally checkable derivation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofDeclineMechanism {
    /// One authored assertion exceeds the per-root bound of the build pass's
    /// own single traversal (`SurfaceWorkModel::Traversal`: node count,
    /// `MAX_SURFACE_DEPTH`, or one root costing more than the whole source
    /// envelope), so proof PRODUCTION is refused before it starts.
    AuthoredSourceRootUnbounded,
    /// Every authored root is individually renderable, but the aggregate
    /// source-work envelope (`MAX_AGGREGATE_SOURCE_WORK`) cannot afford the
    /// build pass.
    AuthoredSourceAggregateBudget,
    /// More than `MAX_PROOF_SOURCE_ROOTS` authored roots / provenance entries.
    AuthoredSourceRootCount,
    /// The proof rested on an `assume false` that the PREPROCESSOR produced by
    /// folding an authored assertion, keeping no record of the rewrite. The
    /// refutation is real and the argument is expressible; it was discarded.
    PreprocessorFoldToFalseUnrecorded,
    /// The bounded surface-override PLAN declined (scan or pair ceiling, the
    /// canonical-root work or binder-shape veto, the source envelope, or the
    /// collector), so no authored spelling exists for the document. Since
    /// #certify-before-presentation a DERIVATION behind the bound is kept and
    /// certified through the canonical authority passes and only the document
    /// is withheld (`Executor::withhold_surface_presentation`); a refutation
    /// with no derivation behind it still gets the one-line trust poison,
    /// which used to replace every proof here before certification read it.
    AuthoredSurfaceOverridePlanUnbounded,
    /// The input-syntax rewrite pass could not afford its own charge against
    /// the shared source-work envelope. Handled as
    /// [`Self::AuthoredSurfaceOverridePlanUnbounded`] is since
    /// #certify-before-presentation; it used to poison the proof outright. Distinct from [`Self::AuthoredSourceAggregateBudget`], which
    /// refuses BEFORE any proof is built.
    InputSyntaxRewriteSourceBudget,
    /// The verdict was admitted by an independently checked SEMANTIC
    /// certificate whose lane nulls `last_proof` by construction. Nothing was
    /// ever rendered — and, measured at the mint (#semantic-token census,
    /// 2026-09-11, 23 of 23 files at two fresh seeds), nothing renderable was
    /// ever held: the token is a list of leaf obligations (22 files: ONE
    /// empty-model evaluation of `true`) over a root that TERM CONSTRUCTION
    /// folded from the authored assertion (`(not (exists ((ts S)) true))`,
    /// 3 nodes, against an authored tree of 119–183 nodes naming 17–19
    /// declared constants). The authored-scope derivation exists only outside
    /// AY — see `scripts/closed_sentence_authored_alethe.py`.
    /// (`unsat_cert.rs::emit_checked_exact_unsat`, previously silent.)
    CheckedSemanticCertificateUnrendered,
    /// The verdict was admitted by an EXACT semantic theorem that seals nested
    /// refutations — the RoundingMode expansion (one probe per branch) or the
    /// closed-sentence theorem (one re-solve per nested obligation) — at least
    /// one of which rests on `discharged-trust`: a fresh-executor re-solve of
    /// the same code whose proof AY's strict checker refused at a trust or
    /// hole step, not an independent check. The theorem is exact; the verdict
    /// is exactly as strong as that refutation, so it is admitted as
    /// `discharged-trust` and nothing here claims a checked certificate.
    /// Before D7's repair (2026-09-23 hunt) this read as
    /// `checked-semantic-certificate-unrendered` and nine wrong answers carried
    /// it; the closed-sentence arm read so until the 2026-09-24 fix-up.
    /// (`unsat_cert.rs::emit_checked_exact_unsat`.)
    ExactExpansionOverDischargedTrust,
    /// The verdict was admitted by the authored-subset theorem
    /// (#qe-ground-first, `unsat_cert/authored_subset.rs`): a refutation of
    /// the authored assertions WITHOUT their top-level universal axioms, sealed
    /// under the class of the probe that refuted them —
    /// `checked-exact-authored-subset`, or `discharged-trust` when that
    /// refutation rests on a trust step. The ordinary proof of that subset was
    /// not installed because its document would not have assumed the problem's
    /// own assertions as written (or none completed within the pass's budget),
    /// so no document is published rather than one an external checker
    /// rejects. (`unsat_cert.rs::emit_checked_exact_unsat`.)
    AuthoredSubsetUnrendered,
    /// A checked refutation existed at publication and was DELETED because its
    /// leaves name solver-invented terms (a CEGQI counterexample constant, a
    /// Skolem witness) that no authored-scope bridge could carry back.
    /// (`quantifier_loop/result_mapping.rs`, previously silent.)
    QuantifierArtifactFirewall,
    /// The last-resort closer restated the SOLVE'S OWN verdict as a single
    /// `Generic` head over the proof's assume-family leaves. Honest, and
    /// unproved: no theory derivation reached the empty clause.
    /// (`proof_resolution/empty_clause.rs`, previously silent. This is the
    /// mechanism behind the floating-point family, whose lane bit-blasts with
    /// proof output OFF and therefore records nothing for the closer to use.)
    AssumeFamilyTrustClosure,
    /// The closer had no assume-family leaf at all and fell back to DERIVED
    /// unit theory-lemma conclusions, where a `Generic` head would be
    /// refutable. `add_validated_head` was asked and declined — none of the
    /// checker's three payload-free recognizers (array theorem, integer cut
    /// lattice gap, integer guarded split gap) re-derives the head from the
    /// clause alone — so a premiseless empty-clause `trust` step was recorded
    /// instead. `verified_finite_enum_witness` says whether a self-verified
    /// finite-enum pigeonhole witness was in hand at that moment and went
    /// unused; when it is `true` the refutation is reconstructable and the
    /// gate is the recogniser, not the evidence.
    /// (`proof_resolution/empty_clause.rs`, previously silent.)
    DerivedLeafTrustClosure {
        /// A self-verified finite-enum pigeonhole witness existed for this
        /// query while the closer was declining.
        verified_finite_enum_witness: bool,
    },
    /// The retained derivation reaches the empty clause through a step AY's
    /// own strict checker refuses (`trust`/`hole`/an unvalidatable theory
    /// lemma). The document's holes are real gaps in the argument, not a
    /// printing limit.
    TerminalTrustStepOnPath,
    /// The retained derivation is trust-free, and the holes in the emitted
    /// document come from the PRINTER: `wire_rule_name` has no pinned-checker
    /// spelling for a rule AY validated, so it downgraded it to `hole`.
    PrinterRuleWithoutExternalSpelling,
    /// The synthesized-default certificate exhausted
    /// `DEFAULT_ALETHE_EMISSION_WORK_BUDGET` mid-render and the whole partial
    /// document was discarded. The derivation itself may be complete.
    AletheEmissionWorkBudget,
    /// The proof is free in symbols an Alethe PROOF document cannot introduce
    /// (`sk!...`, `__ay_symdiff...`, `_divmod_q_...`), or spells one of AY's
    /// own identities no checker resolves: an internal function (the array
    /// `default`, `__ay_overload_N`, `val@Opt!{Int}`) or sort (`Opt!{Int}`,
    /// `__ay_datatype_sort_N`). Pinned Carcara rejects `declare-fun` anywhere
    /// in a proof file, so only `define-fun`-expressible symbols with a
    /// recorded `SkolemChoice` can be introduced.
    UndeclarableProofSymbols,
    /// The rendered surface uses a sort or symbol spelling pinned Carcara
    /// cannot parse (`Seq`, `FloatingPoint`, `Char`, the Z3 escape extension).
    ///
    /// Since owner decision D7 (2026-09-22) this is read off the PUBLISHED
    /// document at disclosure time, not raised by the printer: the document
    /// renders what the strict checker accepted and the CLI's
    /// `c ay.proof.certificate` line carries `carcara_surface=unsupported`
    /// beside it. It is reported only for a derivation that is otherwise
    /// trust-free, so it says why the file is not externally checkable, never
    /// why the refutation lacks a derivation.
    PinnedCheckerSurfaceUnsupported,
    /// One named printing step had no certified bridge to an external rule and
    /// the whole certificate was dropped with it.
    ProofSurfaceBridgeMissing,
    /// The retained proof's authenticated external surface (its finite-enum
    /// override table or its export scope) was absent or stale at render time,
    /// so the exporter refused a proof it otherwise held.
    StaleAuthenticatedExportScope,
    /// The certificate was rendered and could not be WRITTEN (read-only input
    /// directory, full filesystem). Nothing about the derivation is implied.
    CertificateWriteFailed,
    /// The derivation contains a ground-evaluate step whose result is not
    /// portable across term stores, so reconstruction is suppressed rather
    /// than publish a step a re-parse cannot reproduce.
    /// (`proof_rewrite.rs`, previously silent.)
    NonPortableGroundEvaluate,
    /// The proof's reachable `assume` leaves could not be mapped back to the
    /// authored text — no reachable authored root, or no restorable override
    /// map — so the Alethe presentation is suppressed. The derivation itself
    /// survives; what is missing is its authored-scope spelling.
    /// (`proof/authored_congruence_support.rs`, previously silent.)
    AuthoredAssumeSurfaceUnavailable,
    /// A reachable authored `assume` resolved to a source row whose authority
    /// the presentation pass refuses (duplicate canonical roots with
    /// conflicting spellings, or an unauthenticated identity row).
    /// (`proof/authored_congruence_support.rs`, previously silent.)
    AuthoredSourceAuthorityInvalid,
    /// The query ran with parsed-assertion retention OFF — so there is no
    /// authored text to present — while an external proof artifact was
    /// demanded. Nothing is wrong with the derivation; the two settings are
    /// simply incompatible.
    /// (`proof/authored_congruence_support.rs`, previously silent.)
    RetentionOffWithoutAuthoredText,
    /// Two `forall` instances mapped to conflicting authored surfaces, so no
    /// single override table can present them both.
    /// (`proof_rewrite/surface_planning.rs`, previously silent.)
    ForallInstanceSurfaceConflict,
    /// The solve's interrupt or deadline fired while `build_unsat_proof` was
    /// still assembling the derivation, so the half-built proof was replaced
    /// by the fail-closed poison instead of being finished. A stopped solve
    /// publishes `unknown`. (`proof/build_unsat_assembly/stop.rs`.)
    ProofAssemblyStopped,
    /// No derivation was retained and no lane recorded why. This tag is a BUG
    /// REPORT about the attribution, not a diagnosis: a silent site remains.
    NoDerivationRecorded,
}

impl ProofDeclineMechanism {
    /// Stable census tag. Kept kebab-case and machine-greppable on purpose:
    /// this string is what a corpus scan buckets on.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::AuthoredSourceRootUnbounded => "authored-source-root-unbounded",
            Self::AuthoredSourceAggregateBudget => "authored-source-aggregate-budget",
            Self::AuthoredSourceRootCount => "authored-source-root-count",
            Self::PreprocessorFoldToFalseUnrecorded => "preprocessor-fold-to-false",
            Self::AuthoredSurfaceOverridePlanUnbounded => {
                "authored-surface-override-plan-unbounded"
            }
            Self::InputSyntaxRewriteSourceBudget => "input-syntax-rewrite-source-budget",
            Self::CheckedSemanticCertificateUnrendered => "checked-semantic-certificate-unrendered",
            Self::ExactExpansionOverDischargedTrust => "exact-expansion-over-discharged-trust",
            Self::AuthoredSubsetUnrendered => "authored-subset-unrendered",
            Self::QuantifierArtifactFirewall => "quantifier-artifact-firewall",
            Self::AssumeFamilyTrustClosure => "assume-family-trust-closure",
            Self::DerivedLeafTrustClosure {
                verified_finite_enum_witness: false,
            } => "derived-leaf-trust-closure",
            Self::DerivedLeafTrustClosure {
                verified_finite_enum_witness: true,
            } => "derived-leaf-trust-closure-verified-enum-witness-unused",
            Self::TerminalTrustStepOnPath => "terminal-trust-step-on-path",
            Self::PrinterRuleWithoutExternalSpelling => "printer-rule-without-external-spelling",
            Self::AletheEmissionWorkBudget => "alethe-emission-work-budget",
            Self::UndeclarableProofSymbols => "undeclarable-proof-symbols",
            Self::PinnedCheckerSurfaceUnsupported => "pinned-checker-surface-unsupported",
            Self::ProofSurfaceBridgeMissing => "proof-surface-bridge-missing",
            Self::StaleAuthenticatedExportScope => "stale-authenticated-export-scope",
            Self::CertificateWriteFailed => "certificate-write-failed",
            Self::NonPortableGroundEvaluate => "non-portable-ground-evaluate",
            Self::AuthoredAssumeSurfaceUnavailable => "authored-assume-surface-unavailable",
            Self::AuthoredSourceAuthorityInvalid => "authored-source-authority-invalid",
            Self::RetentionOffWithoutAuthoredText => "retention-off-without-authored-text",
            Self::ForallInstanceSurfaceConflict => "forall-instance-surface-conflict",
            Self::ProofAssemblyStopped => "proof-assembly-stopped",
            Self::NoDerivationRecorded => "no-derivation-recorded",
        }
    }

    /// One sentence naming the machinery that would close this gap.
    #[must_use]
    pub const fn explanation(self) -> &'static str {
        match self {
            Self::AuthoredSourceRootUnbounded => {
                "an authored assertion exceeds the per-root bound of the proof build's single traversal, so proof production is refused"
            }
            Self::AuthoredSourceAggregateBudget => {
                "authored roots are individually traversable but the aggregate source-work envelope cannot afford the build pass"
            }
            Self::AuthoredSourceRootCount => {
                "the query has more authored assertion roots than proof reconstruction admits"
            }
            Self::PreprocessorFoldToFalseUnrecorded => {
                "preprocessing refuted an authored assertion by folding it to `false` and kept no derivation for the rewrite"
            }
            Self::AuthoredSurfaceOverridePlanUnbounded => {
                "the bounded authored-surface override plan declined (scan/pair ceiling, canonical-root work or binder shape, envelope, or collector), so no authored-spelling document is written; a derivation standing behind the bound is kept and handed to certification (the no-certificate warning then says so), otherwise the proof is the one-line trust poison"
            }
            Self::InputSyntaxRewriteSourceBudget => {
                "the input-syntax rewrite pass could not afford its charge against the shared source-work envelope, so no authored-spelling document is written; a derivation standing behind the bound is kept and handed to certification (the no-certificate warning then says so), otherwise the proof is the one-line trust poison"
            }
            Self::CheckedSemanticCertificateUnrendered => {
                "an independently checked semantic certificate admitted the verdict; the lane seals leaf obligations over a term-construction residue of the authored assertion and holds no derivation from the authored text to render (the semantic-token census line beside this one says what was held)"
            }
            Self::ExactExpansionOverDischargedTrust => {
                "an exact semantic theorem (a RoundingMode expansion or a closed-sentence refutation) admitted the verdict, but at least one of the nested refutations it seals rests on discharged-trust (a fresh-executor re-solve of the same code whose proof AY's strict checker refused at a trust or hole step, not an independent check), so the verdict is a discharged-trust admission (the semantic-token census line beside this one counts the nested refutations by authority)"
            }
            Self::AuthoredSubsetUnrendered => {
                "a refutation of the authored assertions without their top-level universal axioms (ground-first scheduling) admitted the verdict under the class printed beside this line (checked-exact-authored-subset, or discharged-trust when that refutation rests on a trust step); its derivation could not be rendered assuming only the problem's own assertions as written, so no document is published rather than one an external checker would reject"
            }
            Self::QuantifierArtifactFirewall => {
                "a checked refutation existed at publication and was deleted because its leaves name solver-invented terms outside authored scope"
            }
            Self::AssumeFamilyTrustClosure => {
                "the refutation was closed with a bare trust lemma over the authored assumptions - the theory lane recorded no derivation for the closer to resolve against"
            }
            Self::DerivedLeafTrustClosure {
                verified_finite_enum_witness: false,
            } => {
                "the closer had only derived theory-lemma leaves and no checker recognizer re-derives a head over them, so it recorded a premiseless empty-clause trust step"
            }
            Self::DerivedLeafTrustClosure {
                verified_finite_enum_witness: true,
            } => {
                "the closer recorded a premiseless empty-clause trust step while a self-verified finite-enum pigeonhole witness for this query was in hand and unused"
            }
            Self::TerminalTrustStepOnPath => {
                "the retained derivation reaches the empty clause through a step AY's own strict checker refuses"
            }
            Self::PrinterRuleWithoutExternalSpelling => {
                "the derivation is trust-free and the printer had no pinned-checker spelling for at least one rule AY validated, so it downgraded it to `hole`"
            }
            Self::AletheEmissionWorkBudget => {
                "the synthesized-default certificate exhausted its rendering work budget and the partial document was discarded"
            }
            Self::UndeclarableProofSymbols => {
                "the proof is free in symbols an Alethe proof document cannot introduce (a Skolem constant, or an internal function or sort identity such as the array `default`); the fix is where the symbol is minted or a spelling in the problem's own names, never a declaration"
            }
            Self::PinnedCheckerSurfaceUnsupported => {
                "the document renders and AY's strict checker accepted it, but its surface uses a sort or symbol spelling pinned Carcara cannot parse (carcara_surface=unsupported), so no external checker can confirm it"
            }
            Self::ProofSurfaceBridgeMissing => {
                "one named printing step had no certified bridge to an external rule and the whole certificate was dropped with it"
            }
            Self::StaleAuthenticatedExportScope => {
                "the retained proof's authenticated external surface or export scope was absent or stale at render time"
            }
            Self::CertificateWriteFailed => {
                "the certificate was rendered and could not be written to disk; nothing about the derivation is implied"
            }
            Self::NonPortableGroundEvaluate => {
                "the derivation carries a ground-evaluate step that is not portable across term stores, so reconstruction was suppressed"
            }
            Self::AuthoredAssumeSurfaceUnavailable => {
                "the proof's reachable assume leaves could not be mapped back to the authored text, so its Alethe presentation was suppressed"
            }
            Self::AuthoredSourceAuthorityInvalid => {
                "a reachable authored assume resolved to a source row the presentation pass refuses as unauthenticated"
            }
            Self::RetentionOffWithoutAuthoredText => {
                "the query ran with parsed-assertion retention off, so there is no authored text to present, while an external artifact was demanded"
            }
            Self::ForallInstanceSurfaceConflict => {
                "two forall instances mapped to conflicting authored surfaces, so no single override table can present them both"
            }
            Self::ProofAssemblyStopped => {
                "the solve's interrupt or deadline fired during proof assembly, so the partial derivation was discarded instead of being finished"
            }
            Self::NoDerivationRecorded => {
                "no derivation was retained and no lane recorded why - a silent decline site remains, and this tag is the bug report for it"
            }
        }
    }

    /// Whether the gap this record names is an `assume` leaf with NO AUTHORED
    /// SPELLING — the producer that would have rendered the authored surface
    /// of a root declined, so the document assumes AY's canonical rewriting
    /// of that root instead of the text the problem states.
    ///
    /// The screen in `Executor::live_proof_decline` uses this to tell a
    /// superseded record from a live one. Measured on AUFDTLIRA `P630-039
    /// bug.ads_32_25_range_check` (#probe-ite-lift-promoter): the override
    /// plan recorded [`Self::AuthoredSurfaceOverridePlanUnbounded`], a later
    /// cascade commit replaced the poisoned candidate with a trust-free,
    /// hole-free derivation, and the screen — which asked only whether a
    /// `trust` step remained — dropped the record and let the fallback label
    /// the document `terminal-trust-step-on-path` over a proof with no trust
    /// step on it. The document's single `assume` is still the canonical
    /// root, which is exactly the gap the record describes, so the record is
    /// live, not stale.
    ///
    /// The family is every assembly- or presentation-time decline whose
    /// remedy is an authored rendering of an `assume` (a source-work bound, a
    /// surface-override plan, an unavailable or unauthenticated authored
    /// surface, retention off, conflicting `forall` surfaces). Closure and
    /// document-side records are about steps, not leaves, and stay out.
    #[must_use]
    pub const fn describes_authored_assume_surface(self) -> bool {
        matches!(
            self,
            Self::AuthoredSourceRootUnbounded
                | Self::AuthoredSourceAggregateBudget
                | Self::AuthoredSourceRootCount
                | Self::AuthoredSurfaceOverridePlanUnbounded
                | Self::InputSyntaxRewriteSourceBudget
                | Self::AuthoredAssumeSurfaceUnavailable
                | Self::AuthoredSourceAuthorityInvalid
                | Self::RetentionOffWithoutAuthoredText
                | Self::ForallInstanceSurfaceConflict
        )
    }
}

/// Why SAT-trace reconstruction did not produce the empty clause.
///
/// #closer-population. The reconstruction strategy is the one that ought to
/// carry a bit-blasted refutation into the proof, and when it declines the
/// last-resort closer runs and the verdict ships unevidenced. It said nothing
/// about which of six very different things happened, and the six have nothing
/// in common: no trace at all is a RECORDING gap; a trace that reaches the
/// empty clause and cannot be expressed in terms is a TRANSLATION gap, where
/// AY holds a complete refutation it cannot write down.
///
/// Diagnostic only; no path consults it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SatReconstructionOutcome {
    /// The executor held no clause trace when the pipeline was entered.
    NoTrace,
    /// A trace existed and does not reach the empty clause, so there is no
    /// propositional refutation to carry.
    TraceWithoutEmptyClause,
    /// A trace reaching the empty clause existed and the SAT-variable → term
    /// map (or the negation map) it needs was absent.
    NoVariableMap,
    /// The trace's scope assumptions could not be installed.
    ScopeAssumptionsRejected,
    /// The manager refused the trace outright (`can_process`).
    ManagerDeclinedTrace,
    /// The manager processed the trace and what came back was not an empty
    /// clause. AY held a propositional refutation and the reconstruction
    /// stopped short of expressing it.
    ReconstructionShort,
    /// The empty clause was reconstructed; this strategy closed the proof.
    Reconstructed,
}

impl SatReconstructionOutcome {
    /// Stable census tag, kebab-case and machine-greppable.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::NoTrace => "no-trace",
            Self::TraceWithoutEmptyClause => "trace-without-empty-clause",
            Self::NoVariableMap => "no-variable-map",
            Self::ScopeAssumptionsRejected => "scope-assumptions-rejected",
            Self::ManagerDeclinedTrace => "manager-declined-trace",
            Self::ReconstructionShort => "reconstruction-short",
            Self::Reconstructed => "reconstructed",
        }
    }

    /// How far this outcome got, for the per-query high-water mark.
    ///
    /// The empty-clause pipeline can run more than once on a query, and the
    /// strategy TAKES the clause trace and does not restore it on every path,
    /// so a second run reports `NoTrace` no matter what the first one held.
    /// Keeping the furthest outcome is the only reading that does not turn a
    /// consumed trace into a claim that none existed.
    #[must_use]
    const fn rank(self) -> u8 {
        match self {
            Self::NoTrace => 0,
            Self::TraceWithoutEmptyClause => 1,
            Self::NoVariableMap => 2,
            Self::ScopeAssumptionsRejected => 3,
            Self::ManagerDeclinedTrace => 4,
            Self::ReconstructionShort => 5,
            Self::Reconstructed => 6,
        }
    }
}

/// One SAT-trace reconstruction attempt, and what it was working with.
///
/// #closer-population. Write-only.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SatReconstructionRecord {
    /// How far the attempt got. `None` only before the first attempt.
    pub outcome: Option<SatReconstructionOutcome>,
    /// Entries in the clause trace this attempt held.
    pub trace_entries: u32,
    /// Whether that trace reaches the empty clause.
    pub trace_has_empty: bool,
    /// Variables in the SAT-variable → term map.
    pub mapped_vars: u32,
    /// Trace entries the manager could not express in terms. Counted only when
    /// the attempt reached the manager.
    pub untranslatable_entries: u32,
    /// The search-time proof-bookkeeping work budget (#A2b) ran out during
    /// this query, so the SAT solver stopped recording. The budget is
    /// installed ONLY for synthesized-default certificates — an explicit proof
    /// demand is unbudgeted — which makes this a statement about AY's default
    /// posture and not about what AY can prove.
    pub proof_work_exhausted: bool,
    /// Trace entries were dropped against a memory budget.
    pub trace_truncated: bool,
    /// #destroyed-trace. What the clause trace held at the INSTANT the #A2b
    /// budget degraded it (hints stripped, entries retained literals-only),
    /// measured at the strip site in
    /// `degrade_proof_bookkeeping_after_exhaustion`. Zero when no
    /// degradation happened on this query.
    ///
    /// The 2026-09-08 closure diagnosis described this population as "a
    /// propositional refutation AY recorded and then deliberately discarded"
    /// without measuring the discarded object. `destroyed_has_empty` is the
    /// field that settles it: the budget runs out DURING search, so a trace
    /// that never reached the empty clause is a partial search record, not a
    /// refutation.
    pub destroyed_entries: u32,
    /// Original (input) clauses among [`Self::destroyed_entries`].
    pub destroyed_originals: u32,
    /// Learned clauses among [`Self::destroyed_entries`].
    pub destroyed_learned: u32,
    /// Learned clauses that carried at least one resolution hint.
    pub destroyed_learned_with_hints: u32,
    /// Whether the destroyed trace reached the empty clause.
    pub destroyed_has_empty: bool,
}

impl SatReconstructionRecord {
    /// Keep the attempt that got furthest, ties going to the incumbent.
    pub(crate) fn keep_furthest(&mut self, candidate: Self) {
        let incumbent = self.outcome.map_or(0, SatReconstructionOutcome::rank);
        if candidate.outcome.map_or(0, SatReconstructionOutcome::rank) > incumbent
            || self.outcome.is_none()
        {
            *self = candidate;
        }
    }
}

/// What the proof held at the moment the last-resort closer ran.
///
/// #closer-population. `assume-family-trust-closure` is the largest single
/// class in the campaign's decline census, and the census could not say which
/// of two very different things it names:
///
/// * the theory lane recorded a real derivation and the closer could not chain
///   it to the empty clause — a CHAINING gap, where the reasoning exists; or
/// * the lane recorded nothing at all, so the closer had only the authored
///   assumptions to restate — a RECORDING gap, where there is no reasoning to
///   render.
///
/// The remedies have nothing in common: the first wants another closure
/// strategy, the second wants proof recording turned on in the lane that
/// decided the query. Only a count taken at the closure site tells them apart,
/// because by the time an artifact exists the closer's own chain is all that is
/// left to look at.
///
/// Counted BEFORE the closer adds a step, and write-only: no gate, verdict,
/// certificate, or export reads any field.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TrustClosureCensus {
    /// Steps in the proof when the closer was entered.
    pub steps: u32,
    /// `assume` steps — the proof's record of the authored problem.
    pub assumes: u32,
    /// Premiseless unit `trust` steps: authored assumptions a demotion pass
    /// rewrote, and the other half of the "assume family".
    pub unit_trust_leaves: u32,
    /// `TheoryLemma` steps of any kind — what the theory lanes recorded.
    pub theory_lemmas: u32,
    /// Of those, the ones carrying a kind a strict validator can re-derive
    /// (anything but `Generic`). A lane can record a lemma and still record
    /// nothing checkable.
    pub typed_theory_lemmas: u32,
    /// Steps that are neither an assume-family leaf nor a theory lemma:
    /// resolutions, rule steps, everything the engine derived on top.
    pub derived_steps: u32,
    /// The furthest SAT-trace reconstruction attempt on this query.
    ///
    /// This is the difference between "AY has no refutation to write down" and
    /// "AY has a propositional refutation it cannot express in terms", and the
    /// proof object cannot distinguish them: the trace lives beside the proof,
    /// not in it.
    pub reconstruction: SatReconstructionRecord,
}

impl TrustClosureCensus {
    /// Nothing but the authored assumptions was in the proof.
    ///
    /// This is the RECORDING gap: the closer had no derivation to resolve
    /// against, so no closure strategy could have succeeded on this proof, and
    /// the repair belongs upstream in whichever lane decided the query without
    /// recording steps.
    #[must_use]
    pub const fn is_assumptions_only(self) -> bool {
        self.theory_lemmas == 0 && self.derived_steps == 0
    }

    /// A complete propositional refutation was in hand when the closer ran.
    ///
    /// Where this and [`Self::is_assumptions_only`] are both true, the decline
    /// is a TRANSLATION gap, not a reasoning gap: AY refuted the query and the
    /// refutation exists, in SAT variables, outside the proof object.
    #[must_use]
    pub const fn has_propositional_refutation(self) -> bool {
        self.reconstruction.trace_entries > 0 && self.reconstruction.trace_has_empty
    }
}

/// Whether the sealed root of a checked semantic certificate could be paired
/// with the parsed (authored) assertion it claims to refute.
///
/// #semantic-token census. `Aligned` is the only value under which the
/// authored-scope question is even decidable; every other value says why the
/// pairing was unavailable, and a census must count those apart rather than
/// fold them into either answer.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum SemanticTokenSource {
    /// The certificate kind carries no single sealed root to pair (the
    /// exists / forall-exists / finite-expansion families), so no authored
    /// comparison was attempted.
    #[default]
    NotApplicable,
    /// Parsed-assertion retention is off for this query; the authored text
    /// was never kept.
    RetentionOff,
    /// The parsed ledger, the provenance originals and the token's roots do
    /// not have the same length, so an index pairing would be a guess.
    Misaligned,
    /// The sealed root is not one of the provenance originals — the token's
    /// scope check should make this unreachable, and it is recorded rather
    /// than assumed.
    RootNotInOriginals,
    /// The sealed root was paired with the parsed assertion at its own index.
    Aligned,
}

impl SemanticTokenSource {
    /// Stable census tag.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::NotApplicable => "not-applicable",
            Self::RetentionOff => "retention-off",
            Self::Misaligned => "misaligned",
            Self::RootNotInOriginals => "root-not-in-originals",
            Self::Aligned => "aligned",
        }
    }
}

/// What the exact semantic-certificate mint held at publication.
///
/// #semantic-token census. `checked-semantic-certificate-unrendered` is, by
/// its name, the campaign's structural thesis in its purest form: a checked
/// derivation that only lacks a writer. This record exists to test that name
/// against the object itself. It answers two questions the decline tag cannot:
///
/// 1. **What is the checked object?** For the closed-sentence family it is a
///    list of *obligations* — each a single empty-model evaluation or one
///    nested re-solve — over the sealed root. Their count and kinds are the
///    whole "derivation"; there is no step chain behind them.
/// 2. **Is the sealed root the authored assertion?** The partition that admits
///    this family forbids declared symbols in the sealed root, so if the
///    parsed assertion at the same index names any declared symbol, the root
///    is a construction-time residue of it and not the sentence the user
///    wrote. A producer rendering such a root would certify a theorem nobody
///    asserted.
///
/// Counted at the mint, BEFORE the token is wrapped, and write-only: no gate,
/// verdict, certificate, or export reads any field.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SemanticTokenCensus {
    /// Which exact semantic certificate family minted the token.
    pub kind: &'static str,
    /// Closed-sentence family: sealed obligations in the token.
    pub obligations: u32,
    /// Of those, `evaluate_term(empty model) == true` leaves.
    pub ground_true: u32,
    /// Of those, `evaluate_term(empty model) == false` leaves.
    pub ground_false: u32,
    /// Of those, "the pinned sentence itself was re-refuted by a nested
    /// fresh-executor solve" leaves.
    pub nested_refuted: u32,
    /// Of those, "the pinned sentence's fresh negation was re-refuted by a
    /// nested fresh-executor solve" leaves.
    pub nested_negation_refuted: u32,
    /// Nested refutations that rest on `discharged-trust` — a RoundingMode
    /// branch probe published on it, or a closed-sentence obligation whose
    /// re-solve was accepted only at a trust or hole step — counted apart from
    /// `nested_refuted` / `nested_negation_refuted` (checked ones) because they
    /// are not an independent check.
    pub nested_trust_refuted: u32,
    /// Tree-node count of the sealed root (capped).
    pub sealed_root_nodes: u32,
    /// Head symbol of the sealed root.
    pub sealed_root_head: String,
    /// The sealed root, rendered and truncated for a census line.
    pub sealed_root_surface: String,
    /// Whether the authored comparison below could be made at all.
    pub authored_source: SemanticTokenSource,
    /// Distinct declared symbols the parsed assertion mentions outside any
    /// binder that shadows them. Meaningful only when `authored_source` is
    /// `Aligned`.
    pub authored_symbols: u32,
    /// Tree-node count of the parsed assertion (capped). Meaningful only when
    /// `authored_source` is `Aligned`.
    pub authored_nodes: u32,
    /// Head symbol of the parsed assertion. Meaningful only when
    /// `authored_source` is `Aligned`.
    pub authored_head: String,
    /// Whether the walk over the parsed assertion modelled every node. An
    /// incomplete walk can under-count symbols, so its `authored_symbols == 0`
    /// proves nothing.
    pub authored_walk_complete: bool,
}

impl SemanticTokenCensus {
    /// The sealed root is provably NOT the authored assertion: the authored
    /// text names declared symbols and the sealed root, by the partition that
    /// admitted it, names none. Term construction erased them.
    ///
    /// `Some(true)` is definitive in the negative direction. `Some(false)`
    /// means only that a complete walk found no declared symbol in the
    /// authored text — this test did not refute authored scope, and it is not
    /// a proof of it. `None` when the comparison could not be made.
    #[must_use]
    pub fn sealed_root_is_construction_residue(&self) -> Option<bool> {
        match self.authored_source {
            SemanticTokenSource::Aligned if self.authored_symbols > 0 => Some(true),
            SemanticTokenSource::Aligned if self.authored_walk_complete => Some(false),
            _ => None,
        }
    }

    /// Every obligation in the token is a single-leaf instrument: an
    /// empty-model evaluation or one nested re-solve. There is no chained
    /// derivation to render; what a renderer would print is the leaves.
    #[must_use]
    pub const fn is_leaf_only(&self) -> bool {
        self.obligations
            == self.ground_true
                + self.ground_false
                + self.nested_refuted
                + self.nested_negation_refuted
                + self.nested_trust_refuted
    }
}
