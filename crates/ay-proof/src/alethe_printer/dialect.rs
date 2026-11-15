// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which Carcara a rendered Alethe document is spelled for, where the two
//! checkers AY is replayed with disagree, and what a render printed that only
//! one of them accepts.
//!
//! Two checkers read AY's certificates. Pinned Carcara 1.1.0 (git 9a352ee,
//! `reference/tools.toml`) is the external checker AY's own gates replay
//! with. Clean's vendored Carcara is what external-codegen promotes on (`clean cert
//! verify-external`). Both re-derive a rule's expected term and compare it
//! syntactically, and they differ on three spellings and one rule:
//!
//! * The final layer of `bitblast_ashr`. Pinned Carcara builds
//!   `(ite y_ult_size bit false)` for every shift; Clean builds
//!   `(ite y_ult_size bit sign)`, as SMT-LIB `bvashr` requires. No spelling
//!   satisfies both when the sign bit is not literally `false`. Inside the
//!   admission guards (a sign bit that is literally `false`, or an amount
//!   that cannot reach the width) the two circuits denote the same function,
//!   so either spelling is a TRUE conclusion there; outside them the zero fill
//!   is false, and AY never prints the step there.
//! * `zero_extend`. Where AY keeps Clean's consumer reading
//!   `dialect:expand_zero_extend` ([`CleanOnlySpelling::consumer_rule`]), it
//!   uses only `(= ((_ zero_extend k) x) (concat Z x))` with `Z` the all-zero
//!   word of width `k` (or `x` for `k = 0`) as a `refl` identity. Pinned
//!   Carcara retains the indexed operator and refuses that symbolic `refl`.
//!   It does check closed `evaluate` cases. The packed word lane prints them
//!   in both dialects for a source width of at most eight, and in the pinned
//!   dialect for a wider source with at most eight distinct symbolic bits.
//!   The packed-circuit lane uses that same support bound in both dialects,
//!   sharing a closed universal theorem and checking each `forall_inst`.
//!   Remaining complete-bitblast and above-bound output keeps the explicit
//!   consumer identity and reports it honestly.
//! * The long-division circuit of `bitblast_udiv` / `bitblast_urem`. Clean
//!   (5390f432b8, printed since e9b297e37) compares against the carry out of
//!   the top bit and keeps the difference `r - y`; pinned Carcara compares
//!   against the carry INTO the top bit and fills the remainder with ones.
//!   Pinned Carcara's circuit is FALSE for most operands (`(bvudiv #x80 #x02)`
//!   evaluates to `#x00`), and it accepts it anyway. It is true on a zero
//!   divisor and on the closed operand pairs it happens to divide correctly;
//!   AY prints it only there (`complete_blast::division`), and keeps Clean's
//!   divider everywhere else. The two coincide only on a literally zero
//!   dividend.
//! * A datatype selector over a constructor, `(= (S (C t_0 .. t_n)) t_i)`.
//!   Clean (4dc90e8ea, DOWNSTREAM row C2) checks it as `dt_project`; pinned
//!   Carcara has no datatype rule at all and answers `unknown rule`, which
//!   voids the whole document. The Clean dialect prints `dt_project`
//!   (`format_dt_project`); the pinned dialect keeps the honest `hole`. So
//!   this is the one difference where the pinned dialect prints no spelling
//!   of the step, only the disclosure that it has none. The rule name is in
//!   `ay_core::CLEAN_DIALECT_ALETHE_RULES`, never in the pinned table, and
//!   the round-trip self-check reads a document against the rule vocabulary
//!   of the dialect it was spelled for ([`AletheDialect::implements_rule`]).
//!
//! [`AletheDialect::Clean`] is the default (475ba9547). A render reports every
//! Clean-only spelling it kept in an [`AletheDialectReport`], and the CLI
//! discloses such a certificate `carcara_surface=clean-dialect` instead of
//! `supported`; the library's `UnsatProofArtifact` carries
//! [`crate::CarcaraSurface::CleanDialect`]. [`AletheDialect::PinnedCarcara`]
//! prints the pinned spelling wherever one exists and is true.
//!
//! The selection and the report are per THREAD, scoped by
//! [`with_alethe_dialect`] and [`capture_alethe_dialect_report`]: the printer
//! is single-threaded, and a thread-local keeps the dozens of export entry
//! points and the lowerings below them unchanged.

use std::cell::Cell;

/// The checker a rendered Alethe document is spelled for, where pinned
/// Carcara 9a352ee and Clean's vendored Carcara disagree. See the module doc.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum AletheDialect {
    /// Clean's vendored Carcara, the checker external-codegen promotes on: the
    /// sign-filled `bitblast_ashr` layer and remaining `zero_extend` identities
    /// read as their definition (`dialect:expand_zero_extend`).
    #[default]
    Clean,
    /// Pinned Carcara 1.1.0 (git 9a352ee): the zero-filled `bitblast_ashr`
    /// layer, pinned Carcara's divider where it is true, and the packed word
    /// and packed-circuit lanes' checked `zero_extend` cases wherever their
    /// existing support bound admits them. A remaining `zero_extend` outside
    /// those lowerings has no pinned spelling, and a divider
    /// step outside that domain has no true one; both keep Clean's spelling,
    /// which the render reports.
    PinnedCarcara,
}

impl AletheDialect {
    /// The command-line spelling (`--alethe-dialect`).
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Clean => "clean",
            Self::PinnedCarcara => "pinned-carcara",
        }
    }

    /// Whether this dialect's checker implements the rule `name`, so a
    /// document spelled for it may name the rule without the checker
    /// answering `unknown rule` (which voids the whole document).
    ///
    /// Pinned Carcara implements [`ay_core::CHECKABLE_ALETHE_RULES`]; Clean's
    /// vendored Carcara implements those and
    /// [`ay_core::CLEAN_DIALECT_ALETHE_RULES`] as well. This is the round-trip
    /// self-check's rule-name gate (`AletheDocumentChecker`). Like
    /// [`ay_core::is_checkable_alethe_rule`] it is a vocabulary predicate: it
    /// says nothing about whether a step that names the rule holds.
    #[must_use]
    pub fn implements_rule(self, name: &str) -> bool {
        ay_core::is_checkable_alethe_rule(name)
            || (matches!(self, Self::Clean) && ay_core::is_clean_dialect_alethe_rule(name))
    }
}

/// A spelling that Clean's vendored Carcara checks and pinned Carcara 9a352ee
/// refuses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CleanOnlySpelling {
    /// A `bitblast_ashr` final layer filled with a sign bit that is not
    /// literally `false`.
    SignFilledAshrOvershift,
    /// `((_ zero_extend k) x)` read as its SMT-LIB definition, `(concat Z x)`
    /// (consumer rule `dialect:expand_zero_extend`).
    ZeroExtendAsConcat,
    /// A `bitblast_udiv` / `bitblast_urem` step spelled with Clean's fixed
    /// long-division circuit, which pinned Carcara refuses unless the
    /// dividend is literally zero.
    FixedDivider,
    /// A datatype selector over a constructor, `(= (S (C t_0 .. t_n)) t_i)`,
    /// checked by Clean's `dt_project` rule, which pinned Carcara does not
    /// implement.
    DatatypeSelectorProject,
    /// Bounded common-addend BV cancellation and canonical literal equality
    /// under Clean's explicit `eq_simplify_bv_offsets` checker capability.
    BvOffsetEqualitySimplify,
    /// Version-one bounded add/subtract literal spines, independently checked
    /// by Clean's explicit `eq_simplify_bv_offset_spines_v1` capability.
    BvOffsetSpinesV1,
    /// Independently checked, bounded full-width BV reconstruction.
    BvReconstructV1,
}

impl CleanOnlySpelling {
    /// Every Clean-only spelling. `dialect_rule_tests` holds it complete
    /// through an exhaustive match: `#[non_exhaustive]` binds only outside
    /// this crate, so a new variant does not compile there until it is named.
    pub const ALL: &'static [Self] = &[
        Self::SignFilledAshrOvershift,
        Self::ZeroExtendAsConcat,
        Self::FixedDivider,
        Self::DatatypeSelectorProject,
        Self::BvOffsetEqualitySimplify,
        Self::BvOffsetSpinesV1,
        Self::BvReconstructV1,
    ];

    /// The consumer rule that admits this spelling, by its key in Clean's
    /// `third-party/carcara/DOWNSTREAM.md`: `dialect:<option>` is the parser
    /// option of a `### Dialect:` entry (set by `Config::clean_dialect()`),
    /// `fix:<n>` row `n` of its soundness-fix table, `extension:C<n>` row
    /// `C<n>` of its completeness-extension table. This names the rule; the
    /// rule itself is stated there and nowhere here.
    ///
    /// `dialect:expand_zero_extend` names the entry Clean's parse-boundary
    /// reading of `zero_extend` adds (parser option `expand_zero_extend`),
    /// which Clean's main does not carry yet (checked 2026-10-08, Clean
    /// `3b4bb1811`). Until it does, Clean reads the operator the same way in
    /// an adapter post-pass from `ba5e28ff5` on
    /// (`crates/proof-replay-consumer/src/bridge/ay_backend/carcara_verify/zero_extend.rs`,
    /// whose module doc states the definition), and no `DOWNSTREAM.md` entry
    /// states it: the key is then the name of the reading, not yet a
    /// citation, and Clean's agreement test (which checks each key against
    /// the options `Config::clean_dialect()` sets) arrives with that entry.
    #[must_use]
    pub const fn consumer_rule(self) -> &'static str {
        match self {
            Self::SignFilledAshrOvershift => "fix:2",
            Self::ZeroExtendAsConcat => "dialect:expand_zero_extend",
            Self::FixedDivider => "fix:1",
            Self::DatatypeSelectorProject => "extension:C2",
            Self::BvOffsetEqualitySimplify => "dialect:eq_simplify_bv_offsets",
            Self::BvOffsetSpinesV1 => "dialect:eq_simplify_bv_offset_spines_v1",
            Self::BvReconstructV1 => "dialect:bv_reconstruct_v1",
        }
    }

    /// Retained historical spelling problems, including cases now checked
    /// entirely by standard rules: the conformance set AY's own disclosure
    /// test and Clean's agreement test both replay. Empty where the set lives
    /// only in AY's disclosure test.
    #[must_use]
    pub const fn conformance_problems(self) -> &'static [&'static str] {
        match self {
            Self::ZeroExtendAsConcat => &ZERO_EXTEND_PROBLEMS,
            Self::BvOffsetEqualitySimplify => &BV_OFFSET_EQUALITY_PROBLEMS,
            Self::BvOffsetSpinesV1 => &BV_OFFSET_SPINES_PROBLEMS,
            Self::BvReconstructV1 => &BV_RECONSTRUCT_PROBLEMS,
            Self::SignFilledAshrOvershift | Self::FixedDivider | Self::DatatypeSelectorProject => {
                &[]
            }
        }
    }

    /// A stable, human-readable description for a disclosure line.
    #[must_use]
    pub const fn describe(self) -> &'static str {
        match self {
            Self::SignFilledAshrOvershift => {
                "a bitblast_ashr step fills its overshift layer with the sign bit"
            }
            Self::ZeroExtendAsConcat => {
                "a zero_extend word is read as its SMT-LIB definition, a concat with a zero \
                 word (consumer rule dialect:expand_zero_extend, read so by Clean from \
                 ba5e28ff5)"
            }
            Self::FixedDivider => {
                "a bitblast_udiv or bitblast_urem step spells Clean's fixed long-division circuit"
            }
            Self::DatatypeSelectorProject => {
                "a datatype selector over a constructor is checked by Clean's dt_project rule"
            }
            Self::BvOffsetEqualitySimplify => {
                "eq_simplify cancels a common BV addend or compares canonical BV literals \
                 (consumer rule dialect:eq_simplify_bv_offsets; requires the updated Clean checker)"
            }
            Self::BvOffsetSpinesV1 => {
                "eq_simplify_bv_offset_spines checks bounded literal add/subtract spines \
                 (consumer rule dialect:eq_simplify_bv_offset_spines_v1; requires explicit version-one support)"
            }
            Self::BvReconstructV1 => {
                "bv_reconstruct_v1 checks aligned disjoint full-width word reconstruction \
                 (consumer rule dialect:bv_reconstruct_v1; requires explicit version-one support)"
            }
        }
    }

    /// Whether [`AletheDialect::PinnedCarcara`] prints a pinned spelling
    /// instead. `false` for [`Self::FixedDivider`]: pinned Carcara's divider
    /// is false for most operands, so the pinned dialect prints it only on a
    /// narrow domain ([`Self::pinned_dialect_note`]). `false` for
    /// [`Self::ZeroExtendAsConcat`] too: the pinned dialect prints closed
    /// cases in the packed word and circuit lanes for a word with at most
    /// eight distinct symbolic bits, so a kept `concat` is outside those
    /// admitted lowerings.
    /// `false` for [`Self::DatatypeSelectorProject`]: pinned Carcara has no
    /// datatype rule, so the pinned dialect prints the step as `hole`.
    #[must_use]
    pub const fn has_pinned_spelling(self) -> bool {
        matches!(self, Self::SignFilledAshrOvershift)
    }

    /// What pinned Carcara and [`AletheDialect::PinnedCarcara`] make of this
    /// spelling, as the tail of a disclosure line.
    #[must_use]
    pub const fn pinned_dialect_note(self) -> &'static str {
        match self {
            Self::SignFilledAshrOvershift => {
                "and `--alethe-dialect pinned-carcara` prints the pinned spelling instead"
            }
            Self::ZeroExtendAsConcat => {
                "and has no rule that spells it (a Clean older than ba5e28ff5 refuses it too)"
            }
            Self::FixedDivider => {
                "and its own divider is false for most operands, so \
                 `--alethe-dialect pinned-carcara` prints it only for a zero divisor \
                 or closed operands it divides correctly"
            }
            Self::DatatypeSelectorProject => {
                "which has no datatype rule (`unknown rule`), so \
                 `--alethe-dialect pinned-carcara` prints the step as an unproved `hole`"
            }
            Self::BvOffsetEqualitySimplify => {
                "which lacks these eq_simplify cases (Clean package 13482 also refuses them), so \
                 `--alethe-dialect pinned-carcara` prints the step as an unproved `hole`"
            }
            Self::BvOffsetSpinesV1 => {
                "which lacks the version-one spine rule (older Clean consumers also refuse it), so \
                 `--alethe-dialect pinned-carcara` prints the step as an unproved `hole`"
            }
            Self::BvReconstructV1 => {
                "which lacks the version-one reconstruction rule (older Clean consumers also refuse it), so \
                 `--alethe-dialect pinned-carcara` prints the step as an unproved `hole`"
            }
        }
    }
}

const BV_RECONSTRUCT_PROBLEMS: [&str; 1] = ["(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
     (assert (not (= ((_ zero_extend 0) ((_ extract 7 0) x)) x)))\n(check-sat)\n"];

const BV_OFFSET_SPINES_PROBLEMS: [&str; 1] =
    ["(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
     (assert (not (= (bvadd (bvadd x (_ bv255 8)) (_ bv1 8)) x)))\n(check-sat)\n"];

const BV_OFFSET_EQUALITY_PROBLEMS: [&str; 1] =
    ["(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
     (assert (= (bvadd x (_ bv255 8)) (bvadd x (_ bv0 8))))\n(check-sat)\n"];

/// [`CleanOnlySpelling::conformance_problems`] for
/// [`CleanOnlySpelling::ZeroExtendAsConcat`], one per lane: z02, a 16-bit
/// word past the packed word lane's closed-case bound (packed `refl`); a byte
/// read back from memory (now checked standard packed-circuit output); the
/// commuted `bvor` of two zero-extended bytes (complete bit-blast `refl`);
/// and a closed-case-sized identity twice under one conjunction (now checked
/// standard packed-circuit output). All four original problems are retained.
const ZERO_EXTEND_PROBLEMS: [&str; 4] = [
    "(set-logic QF_BV)\n(declare-const x (_ BitVec 16))\n\
     (assert (not (= ((_ extract 15 0) (bvlshr ((_ zero_extend 16) x) (_ bv3 32))) \
     (bvlshr x (_ bv3 16)))))\n(check-sat)\n",
    "(set-logic QF_ABV)\n(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))\n\
     (declare-const addr (_ BitVec 64))\n(declare-const v (_ BitVec 8))\n\
     (assert (not (= ((_ zero_extend 24) (select (store a addr v) addr)) \
     ((_ zero_extend 24) v))))\n(check-sat)\n",
    "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(declare-const y (_ BitVec 8))\n\
     (assert (not (= (bvor ((_ zero_extend 8) x) ((_ zero_extend 8) y)) \
     (bvor ((_ zero_extend 8) y) ((_ zero_extend 8) x)))))\n(check-sat)\n",
    "(set-logic QF_BV)\n(declare-const b1 (_ BitVec 8))\n(declare-const b2 (_ BitVec 8))\n\
     (assert (not (and \
     (= ((_ extract 15 0) (bvlshr ((_ zero_extend 16) (concat #x00 b1)) (_ bv3 32))) \
     (bvlshr (concat #x00 b1) (_ bv3 16))) \
     (= ((_ extract 15 0) (bvlshr ((_ zero_extend 16) (concat #x00 b2)) (_ bv2 32))) \
     (bvlshr (concat #x00 b2) (_ bv2 16))))))\n(check-sat)\n",
];

/// The Clean-only spellings one render kept, and whether it eliminated a
/// problem `let` with `:rule let` ([`Self::eliminates_problem_let`]). The
/// default is a document every spelling of which is pinned Carcara's, in
/// either of its gate invocations.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AletheDialectReport {
    kept: u64,
    first: Option<CleanOnlySpelling>,
    let_rules: u64,
}

impl AletheDialectReport {
    /// The first Clean-only spelling the render kept, if any.
    #[must_use]
    pub const fn first_clean_only(&self) -> Option<CleanOnlySpelling> {
        self.first
    }

    /// Clean-only spellings noted by lowerings that produced text. A lowering
    /// that runs more than once for one step notes it more than once, so read
    /// this as "at least one" when it is not zero.
    #[must_use]
    pub const fn clean_only_notes(&self) -> u64 {
        self.kept
    }

    /// Whether every spelling the render kept is pinned Carcara's.
    #[must_use]
    pub const fn is_pinned_spelling(&self) -> bool {
        self.kept == 0
    }

    /// Whether the render eliminated a `let` the problem wrote with a
    /// `:rule let` step (the certified arm of the `let`-assume bridge).
    ///
    /// Pinned Carcara checks such a document only when it is run without
    /// `--expand-let-bindings`: that flag expands the `let` in the problem and
    /// in the proof at parse time, so the step's left side is no longer a
    /// `let` and the rule refuses it (`term '(and ..)' is of the wrong form,
    /// expected '(let ...)'`). No other document is valid in both
    /// invocations: without the flag the `assume` must be the problem's own
    /// `(let ...)`, and only `:rule let` eliminates it. See
    /// [`crate::CarcaraSurface::WithoutLetExpansion`].
    #[must_use]
    pub const fn eliminates_problem_let(&self) -> bool {
        self.let_rules != 0
    }

    const fn merged(self, inner: Self) -> Self {
        Self {
            kept: self.kept.saturating_add(inner.kept),
            first: match self.first {
                Some(first) => Some(first),
                None => inner.first,
            },
            let_rules: self.let_rules.saturating_add(inner.let_rules),
        }
    }
}

thread_local! {
    static DIALECT: Cell<AletheDialect> = const { Cell::new(AletheDialect::Clean) };
    static REPORT: Cell<AletheDialectReport> = const {
        Cell::new(AletheDialectReport { kept: 0, first: None, let_rules: 0 })
    };
}

/// Run `render` with `dialect` selected on this thread, and restore the
/// previous selection afterwards (also when `render` unwinds).
pub fn with_alethe_dialect<R>(dialect: AletheDialect, render: impl FnOnce() -> R) -> R {
    struct Restore(AletheDialect);
    impl Drop for Restore {
        fn drop(&mut self) {
            DIALECT.with(|selected| selected.set(self.0));
        }
    }
    let _restore = Restore(DIALECT.with(|selected| selected.replace(dialect)));
    render()
}

/// Run `render` and return, beside its result, the Clean-only spellings the
/// renders inside it kept. Nested captures also report to the enclosing one.
pub fn capture_alethe_dialect_report<R>(render: impl FnOnce() -> R) -> (R, AletheDialectReport) {
    struct Merge(AletheDialectReport);
    impl Drop for Merge {
        fn drop(&mut self) {
            REPORT.with(|report| report.set(self.0.merged(report.get())));
        }
    }
    let merge = Merge(REPORT.with(|report| report.replace(AletheDialectReport::default())));
    let result = render();
    let captured = REPORT.with(Cell::get);
    drop(merge);
    (result, captured)
}

impl crate::CarcaraSurface {
    /// This surface verdict, with what `report` says the render printed: a
    /// [`Self::Supported`] document that kept a Clean-only spelling is
    /// [`Self::CleanDialect`] (pinned Carcara refuses it in every
    /// invocation), and one that eliminated a problem `let` with `:rule let`
    /// is [`Self::WithoutLetExpansion`]. An unparseable document stays
    /// [`Self::Unsupported`], which already refuses it.
    #[must_use]
    pub fn with_dialect_report(self, report: &AletheDialectReport) -> Self {
        match (self, report.first_clean_only()) {
            (Self::Supported, Some(spelling)) => Self::CleanDialect { spelling },
            (Self::Supported, None) if report.eliminates_problem_let() => Self::WithoutLetExpansion,
            (surface, _) => surface,
        }
    }
}

/// The dialect selected on this thread.
pub(crate) fn current() -> AletheDialect {
    DIALECT.with(Cell::get)
}

/// Record that the text being built keeps `spelling`. Only lowerings that
/// produce text keep what they noted (see [`attempt`]).
pub(crate) fn note_clean_only(spelling: CleanOnlySpelling) {
    REPORT.with(|report| {
        report.set(report.get().merged(AletheDialectReport {
            kept: 1,
            first: Some(spelling),
            let_rules: 0,
        }));
    });
}

/// Record that the text being built eliminates a problem `let` with
/// `:rule let` ([`AletheDialectReport::eliminates_problem_let`]).
pub(crate) fn note_problem_let_rule() {
    REPORT.with(|report| {
        report.set(report.get().merged(AletheDialectReport {
            kept: 0,
            first: None,
            let_rules: 1,
        }));
    });
}

/// Run one lowering attempt. What it noted is kept only when it produced
/// text: a declined lane contributes nothing to the document, so it must
/// contribute nothing to the report either.
pub(crate) fn attempt<T>(lane: impl FnOnce() -> Option<T>) -> Option<T> {
    let before = REPORT.with(Cell::get);
    let produced = lane();
    if produced.is_none() {
        REPORT.with(|report| report.set(before));
    }
    produced
}

/// Run a support preflight that renders only to answer a question. Nothing
/// it notes is kept.
pub(crate) fn discarding_notes<R>(preflight: impl FnOnce() -> R) -> R {
    let before = REPORT.with(Cell::get);
    let answer = preflight();
    REPORT.with(|report| report.set(before));
    answer
}

#[cfg(test)]
#[path = "dialect_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "dialect_rule_tests.rs"]
mod rule_tests;
