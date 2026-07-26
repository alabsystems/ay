// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed, fail-closed validation for retroactive competition score reports.
//!
//! A structurally validated packet is the exact join of three independently
//! versioned documents:
//!
//! * the continuous competition catalog (`continuous-2025-2026.toml`);
//! * a normalized official field, with one leaderboard per catalog track; and
//! * an AY score report, with one score disposition per catalog track.
//!
//! Scores remain [`serde_json::Value`] because competition scores are not all
//! scalar: several are lexicographic records or vectors. A complete `scored`
//! field is admitted only when this module has a typed comparator for its
//! catalog score kind. The validator parses every official and AY score with
//! that comparator and recomputes ranks and win state rather than trusting a
//! submitted rank.
//!
//! An official `partial` disposition preserves a verified public subset such
//! as a top-N table or values recovered from a plot. That subset is useful
//! evidence, but it is deliberately insufficient for an AY score, rank, or
//! retroactive-win claim. Only a complete `scored` official field can admit a
//! scored AY row.
//!
//! An official `unmaterialized` disposition records the narrower case where a
//! final leaderboard or result source exists and is evidence-bound, but no
//! competitors have yet been normalized from it. `pending-normalization`
//! instead means the catalog row is final but no official artifact has been
//! frozen yet. It is distinct from `pending`, which means required official
//! publication is still outstanding.
//!
//! Both longitudinal JSON documents name their upstream artifacts. The
//! combined loader hashes the exact catalog and official-field bytes it parsed,
//! verifies the declared SHA-256 values, and requires the AY and official
//! reports to identify the same catalog.

use std::cmp::Ordering;
use std::collections::{BTreeMap, HashSet};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use thiserror::Error;

/// The only document schema currently understood by this module.
pub const CAMPAIGN_SCHEMA_VERSION: u32 = 1;

/// The catalog fields needed to validate normalized competition reports.
///
/// The source catalog intentionally contains additional research metadata.
/// Serde therefore accepts additional TOML keys here, while the two normalized
/// JSON formats below deny unknown fields.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ContinuousCatalog {
    /// Catalog schema version.
    pub schema_version: u32,
    /// Declared inventory scope; this is surfaced with every structural check.
    pub scope: String,
    /// Canonical competition tracks.
    #[serde(rename = "track")]
    pub tracks: Vec<CatalogTrack>,
}

/// A catalog row relevant to score-report validation.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct CatalogTrack {
    /// Canonical lowercase kebab-case track identifier.
    pub id: String,
    /// Official catalog status.
    pub status: String,
    /// Artifact and result readiness.
    pub readiness: String,
    /// Competition-specific primary score representation.
    pub official_score_kind: String,
    /// Whether the primary score is minimized, maximized, mixed, or inapplicable.
    pub official_score_direction: String,
    /// AY's solver-side adapter status.
    pub ay_adapter_status: String,
}

/// Normalized official leaderboards for the catalog.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct OfficialFieldReport {
    /// Official-field schema version.
    pub schema_version: u32,
    /// Timestamp at which this normalized field was generated.
    pub generated_at: String,
    /// Exact continuous-catalog artifact used for normalization.
    pub catalog: CampaignIdentity,
    /// Exactly one leaderboard for every catalog track.
    pub leaderboards: Vec<OfficialLeaderboard>,
}

/// One normalized official leaderboard.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct OfficialLeaderboard {
    /// Canonical catalog track identifier.
    pub track_id: String,
    /// Whether this leaderboard is complete, partial, pending, or inapplicable.
    #[serde(alias = "status")]
    pub disposition: ScoreDisposition,
    /// The official field. This must be empty unless `disposition` is
    /// [`ScoreDisposition::Scored`] or [`ScoreDisposition::Partial`].
    pub competitors: Vec<OfficialCompetitor>,
    /// Exact official instance denominator for this score view. Required for
    /// a complete scored field and forbidden when no field was published.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub denominator: Option<u64>,
    /// Hash-bound source artifacts used to normalize this leaderboard.
    pub evidence: Vec<CampaignIdentity>,
}

/// One competitor in a normalized official leaderboard.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct OfficialCompetitor {
    /// Published rank. Ranks start at one.
    pub rank: u64,
    /// Published solver or entrant name.
    pub name: String,
    /// Whether this entry is eligible to win this leaderboard.
    pub eligible: bool,
    /// Whether this entry is an official winner after applying eligibility.
    pub winner: bool,
    /// Explicit acknowledgement that another competitor shares this rank.
    pub tied: bool,
    /// Competition-specific primary score.
    pub score: Value,
    /// Competition-specific solved counts and tie-break metrics.
    pub metrics: Value,
}

/// AY's normalized score report.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AyScoreReport {
    /// AY score-report schema version.
    pub schema_version: u32,
    /// Timestamp at which this score report was generated.
    pub generated_at: String,
    /// Exact continuous-catalog artifact used for this report.
    pub catalog: CampaignIdentity,
    /// Exact normalized official-field artifact used for ranking.
    pub official_field: CampaignIdentity,
    /// Exactly one row for every catalog track.
    pub rows: Vec<AyScoreRow>,
}

/// One AY score or non-score disposition.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AyScoreRow {
    /// Canonical catalog track identifier.
    pub track_id: String,
    /// Whether AY has a verified score for this track.
    #[serde(alias = "status")]
    pub disposition: ScoreDisposition,
    /// Competition-specific score. Required only for a scored row.
    #[serde(default)]
    pub score: Option<Value>,
    /// Solved count and denominator. Required only for a scored row.
    #[serde(default)]
    pub solves: Option<SolveSummary>,
    /// Retroactive rank after inserting AY into the eligible official field.
    #[serde(default)]
    pub rank: Option<u64>,
    /// Whether the reported rank is a retroactive win.
    #[serde(default)]
    pub win: Option<bool>,
    /// Candidate source/binary identity.
    #[serde(default)]
    pub candidate: Option<CampaignIdentity>,
    /// Exact corpus/selection identity.
    #[serde(default)]
    pub corpus: Option<CampaignIdentity>,
    /// Competition scorer and version identity.
    #[serde(default)]
    pub scorer: Option<CampaignIdentity>,
    /// Independent checker packet identity.
    #[serde(default)]
    pub checker: Option<CampaignIdentity>,
    /// Enforced resource-envelope identity.
    #[serde(default)]
    pub envelope: Option<CampaignIdentity>,
    /// Hash-bound run records and result artifacts.
    #[serde(default)]
    pub evidence: Vec<CampaignIdentity>,
}

/// Solved count and rate for an AY score row.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SolveSummary {
    /// Number of validly solved instances.
    pub solved: u64,
    /// Exact official denominator for this score view.
    pub total: u64,
    /// `solved / total`, or zero when `total` is zero.
    pub solve_rate: f64,
}

/// A stable identity for an input, executable, ruleset, or evidence artifact.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CampaignIdentity {
    /// Stable identifier, such as a commit, ruleset version, or artifact URI.
    pub id: String,
    /// Optional lowercase hexadecimal SHA-256 digest.
    #[serde(default)]
    pub sha256: Option<String>,
}

/// A normalized score disposition.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ScoreDisposition {
    /// A verified score, solve rate, rank, and evidence packet are present.
    Scored,
    /// A nonempty, verified subset of the official field is public, but the
    /// field is too incomplete to support an AY rank or win claim.
    Partial,
    /// A final official leaderboard/source exists and is evidence-bound, but
    /// its competitor field has not yet been normalized.
    Unmaterialized,
    /// The catalog row is final, but no official result artifact has yet been
    /// frozen for normalization.
    PendingNormalization,
    /// Required official artifacts or an AY replay are not complete.
    Pending,
    /// The competition or track was cancelled.
    Cancelled,
    /// The track was not held or was omitted.
    NotHeld,
    /// The event existed but did not publish this ranking.
    NotRanked,
    /// AY cannot execute or independently validate this track.
    Unsupported,
}

impl ScoreDisposition {
    fn has_published_field(self) -> bool {
        matches!(self, Self::Scored | Self::Partial)
    }

    fn allows_ay_score(self) -> bool {
        self == Self::Scored
    }
}

impl fmt::Display for ScoreDisposition {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Scored => "scored",
            Self::Partial => "partial",
            Self::Unmaterialized => "unmaterialized",
            Self::PendingNormalization => "pending-normalization",
            Self::Pending => "pending",
            Self::Cancelled => "cancelled",
            Self::NotHeld => "not-held",
            Self::NotRanked => "not-ranked",
            Self::Unsupported => "unsupported",
        };
        formatter.write_str(text)
    }
}

/// Which input document produced a validation issue.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CampaignDocument {
    /// The continuous TOML catalog.
    Catalog,
    /// The normalized official-field JSON.
    OfficialField,
    /// The AY score-report JSON.
    AyScoreReport,
}

impl fmt::Display for CampaignDocument {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Catalog => "continuous catalog",
            Self::OfficialField => "official field",
            Self::AyScoreReport => "AY score report",
        })
    }
}

/// One independently actionable report-validation failure.
#[derive(Clone, Debug, Error, PartialEq)]
#[non_exhaustive]
pub enum CampaignValidationIssue {
    /// A document is not schema version 1.
    #[error("{document} has schema_version={found}; expected {expected}")]
    SchemaVersion {
        /// Failing document.
        document: CampaignDocument,
        /// Parsed version.
        found: u32,
        /// Supported version.
        expected: u32,
    },

    /// A longitudinal report timestamp is not canonical second-resolution UTC.
    #[error("{document} has invalid generated_at value {value:?}")]
    InvalidGeneratedAt {
        /// Failing document.
        document: CampaignDocument,
        /// Invalid timestamp text.
        value: String,
    },

    /// A required top-level report identity is malformed.
    #[error("{document} has invalid {field} identity {id:?}")]
    InvalidReportIdentity {
        /// Failing document.
        document: CampaignDocument,
        /// Identity role.
        field: &'static str,
        /// Invalid identity.
        id: String,
    },

    /// A top-level report identity lacks a content digest.
    #[error("{document} {field} identity has no SHA-256 digest")]
    MissingReportSha256 {
        /// Failing document.
        document: CampaignDocument,
        /// Identity role.
        field: &'static str,
    },

    /// A top-level report identity has a malformed content digest.
    #[error("{document} has invalid {field} SHA-256 {sha256:?}")]
    InvalidReportSha256 {
        /// Failing document.
        document: CampaignDocument,
        /// Identity role.
        field: &'static str,
        /// Invalid digest.
        sha256: String,
    },

    /// AY and the official field name different catalog artifacts.
    #[error("AY catalog identity does not exactly match the official-field catalog identity")]
    CatalogIdentityMismatch,

    /// The continuous catalog contains no tracks.
    #[error("continuous catalog has no track rows")]
    EmptyCatalog,

    /// The catalog scope is empty, padded, or contains control characters.
    #[error("continuous catalog has invalid scope {value:?}")]
    InvalidCatalogScope {
        /// Invalid scope text.
        value: String,
    },

    /// A required catalog field is empty, padded, or contains control characters.
    #[error("catalog track {track_id:?} has invalid {field} value {value:?}")]
    InvalidCatalogField {
        /// Track identifier.
        track_id: String,
        /// Invalid field.
        field: &'static str,
        /// Invalid value.
        value: String,
    },

    /// The catalog score direction is outside the schema's closed vocabulary.
    #[error("catalog track {track_id:?} has unsupported official_score_direction {direction:?}")]
    UnknownOfficialScoreDirection {
        /// Track identifier.
        track_id: String,
        /// Unsupported direction.
        direction: String,
    },

    /// The catalog AY adapter state is outside the schema's closed vocabulary.
    #[error("catalog track {track_id:?} has unsupported ay_adapter_status {status:?}")]
    UnknownAyAdapterStatus {
        /// Track identifier.
        track_id: String,
        /// Unsupported adapter state.
        status: String,
    },

    /// A track ID is not canonical lowercase kebab case.
    #[error("{document} contains non-canonical track id {track_id:?}")]
    NonCanonicalTrackId {
        /// Failing document.
        document: CampaignDocument,
        /// Invalid identifier.
        track_id: String,
    },

    /// A document contains the same track ID more than once.
    #[error("{document} contains duplicate track id {track_id:?}")]
    DuplicateTrackId {
        /// Failing document.
        document: CampaignDocument,
        /// Duplicate identifier.
        track_id: String,
    },

    /// A normalized report references a track absent from the catalog.
    #[error("{document} contains unknown track id {track_id:?}")]
    UnknownTrackId {
        /// Failing document.
        document: CampaignDocument,
        /// Unknown identifier.
        track_id: String,
    },

    /// A normalized report omits a catalog row.
    #[error("{document} is missing catalog track {track_id:?}")]
    MissingTrackId {
        /// Failing document.
        document: CampaignDocument,
        /// Missing identifier.
        track_id: String,
    },

    /// The catalog introduced a status this schema cannot normalize safely.
    #[error("catalog track {track_id:?} has unsupported status {status:?}")]
    UnknownCatalogStatus {
        /// Track identifier.
        track_id: String,
        /// Unrecognized catalog status.
        status: String,
    },

    /// The official disposition contradicts the catalog status.
    #[error(
        "official field track {track_id:?} has disposition {found}; catalog permits {allowed}"
    )]
    OfficialDispositionMismatch {
        /// Track identifier.
        track_id: String,
        /// Allowed normalized dispositions.
        allowed: &'static str,
        /// Reported disposition.
        found: ScoreDisposition,
    },

    /// AY used a disposition incompatible with the official field.
    #[error("AY track {track_id:?} has disposition {found}; official disposition is {official}")]
    AyDispositionMismatch {
        /// Track identifier.
        track_id: String,
        /// Official disposition.
        official: ScoreDisposition,
        /// AY disposition.
        found: ScoreDisposition,
    },

    /// AY claimed a score for a catalog row whose adapter is not ready.
    #[error(
        "AY track {track_id:?} is scored but catalog ay_adapter_status is {adapter_status:?}; expected \"ready\""
    )]
    AyAdapterNotReady {
        /// Track identifier.
        track_id: String,
        /// Catalog adapter state.
        adapter_status: String,
    },

    /// A non-scored official row contains competitors.
    #[error(
        "official field track {track_id:?} has disposition {disposition} but contains competitors"
    )]
    CompetitorsForbidden {
        /// Track identifier.
        track_id: String,
        /// Non-scored disposition.
        disposition: ScoreDisposition,
    },

    /// A scored or partial official row has no competitors.
    #[error("scored/partial official field track {track_id:?} has no competitors")]
    EmptyOfficialField {
        /// Track identifier.
        track_id: String,
    },

    /// A scored or partial official row has no eligible rank-one competitor.
    #[error(
        "scored/partial official field track {track_id:?} has no eligible rank-one competitor"
    )]
    NoEligibleCompetitor {
        /// Track identifier.
        track_id: String,
    },

    /// A competitor name is empty, padded, or contains control characters.
    #[error("official field track {track_id:?} has invalid competitor name {name:?}")]
    InvalidCompetitorName {
        /// Track identifier.
        track_id: String,
        /// Invalid name.
        name: String,
    },

    /// Competitor names are not unique within a leaderboard.
    #[error("official field track {track_id:?} repeats competitor name {name:?}")]
    DuplicateCompetitorName {
        /// Track identifier.
        track_id: String,
        /// Duplicate name.
        name: String,
    },

    /// Published ranks must start at one.
    #[error("official field track {track_id:?} gives {name:?} rank zero")]
    InvalidCompetitorRank {
        /// Track identifier.
        track_id: String,
        /// Competitor name.
        name: String,
    },

    /// An official score is absent or JSON null.
    #[error("official field track {track_id:?} has no score for {name:?}")]
    MissingOfficialScore {
        /// Track identifier.
        track_id: String,
        /// Competitor name.
        name: String,
    },

    /// A complete official field omits its instance denominator.
    #[error("scored official field track {track_id:?} has no instance denominator")]
    MissingOfficialDenominator {
        /// Track identifier.
        track_id: String,
    },

    /// An official field declares an unusable instance denominator.
    #[error("official field track {track_id:?} has invalid instance denominator {denominator}")]
    InvalidOfficialDenominator {
        /// Track identifier.
        track_id: String,
        /// Invalid zero denominator.
        denominator: u64,
    },

    /// A disposition with no published field declares a denominator.
    #[error(
        "official field track {track_id:?} has disposition {disposition} but declares a denominator"
    )]
    OfficialDenominatorForbidden {
        /// Track identifier.
        track_id: String,
        /// Disposition that cannot carry a denominator.
        disposition: ScoreDisposition,
    },

    /// A complete field uses a score kind for which no checked comparator exists.
    #[error(
        "scored official field track {track_id:?} uses unregistered score comparator {score_kind:?}"
    )]
    UnsupportedScoreComparator {
        /// Track identifier.
        track_id: String,
        /// Catalog score kind.
        score_kind: String,
    },

    /// A registered score kind has a contradictory catalog direction.
    #[error(
        "catalog track {track_id:?} score kind {score_kind:?} requires direction {expected:?}, found {found:?}"
    )]
    ScoreDirectionMismatch {
        /// Track identifier.
        track_id: String,
        /// Catalog score kind.
        score_kind: String,
        /// Comparator's required direction.
        expected: &'static str,
        /// Catalog direction.
        found: String,
    },

    /// A typed official score could not be decoded or violates its schema.
    #[error("official field track {track_id:?} has invalid score for {name:?}: {reason}")]
    InvalidOfficialScore {
        /// Track identifier.
        track_id: String,
        /// Competitor name.
        name: String,
        /// Score parsing or range failure.
        reason: String,
    },

    /// A complete official rank disagrees with the registered comparator.
    #[error(
        "official field track {track_id:?} gives {name:?} rank {reported}; registered scorer recomputes rank {expected}"
    )]
    OfficialScoreRankMismatch {
        /// Track identifier.
        track_id: String,
        /// Competitor name.
        name: String,
        /// Published rank.
        reported: u64,
        /// Rank recomputed from the normalized field.
        expected: u64,
    },

    /// Current schema cannot safely rank an ineligible complete-field entry.
    #[error(
        "scored official field track {track_id:?} contains ineligible entry {name:?}; use a separately normalized award field"
    )]
    UnsupportedScoredEligibility {
        /// Track identifier.
        track_id: String,
        /// Ineligible entry.
        name: String,
    },

    /// A duplicate rank was not explicitly marked as a tie by every member.
    #[error(
        "official field track {track_id:?} shares rank {rank} without an explicit tie on every entry"
    )]
    RankTieNotExplicit {
        /// Track identifier.
        track_id: String,
        /// Shared rank.
        rank: u64,
    },

    /// A singleton rank is incorrectly marked as tied.
    #[error("official field track {track_id:?} marks singleton rank {rank} as tied")]
    SpuriousRankTie {
        /// Track identifier.
        track_id: String,
        /// Singleton rank.
        rank: u64,
    },

    /// Distinct published ranks do not use standard competition ranking.
    #[error(
        "official field track {track_id:?} has rank {found}; expected {expected} after the preceding tie group"
    )]
    InvalidCompetitionRankSequence {
        /// Track identifier.
        track_id: String,
        /// Expected next distinct rank.
        expected: u64,
        /// Published next distinct rank.
        found: u64,
    },

    /// The explicit winner flag does not match eligibility and best rank.
    #[error(
        "official field track {track_id:?} has inconsistent winner flag for {name:?}: expected {expected}"
    )]
    OfficialWinnerMismatch {
        /// Track identifier.
        track_id: String,
        /// Competitor name.
        name: String,
        /// Winner value implied by eligibility and rank.
        expected: bool,
    },

    /// A final official leaderboard row has no source evidence.
    #[error("official field track {track_id:?} requires a nonempty evidence identity")]
    MissingOfficialEvidence {
        /// Track identifier.
        track_id: String,
    },

    /// An official disposition that represents no frozen artifact contains evidence.
    #[error(
        "official field track {track_id:?} has disposition {disposition} but contains evidence"
    )]
    OfficialEvidenceForbidden {
        /// Track identifier.
        track_id: String,
        /// Disposition that forbids evidence.
        disposition: ScoreDisposition,
    },

    /// A non-scored AY row contains a result claim.
    #[error(
        "AY track {track_id:?} has disposition {disposition} but contains forbidden field {field:?}"
    )]
    AyClaimForbidden {
        /// Track identifier.
        track_id: String,
        /// Non-scored disposition.
        disposition: ScoreDisposition,
        /// Present result field.
        field: &'static str,
    },

    /// A scored AY row omits a required value or identity.
    #[error("scored AY track {track_id:?} is missing required field {field:?}")]
    MissingAyScoredField {
        /// Track identifier.
        track_id: String,
        /// Missing field.
        field: &'static str,
    },

    /// The solve counts cannot produce the reported rate.
    #[error("AY track {track_id:?} has invalid solve summary: {reason}")]
    InvalidSolveSummary {
        /// Track identifier.
        track_id: String,
        /// Human-readable arithmetic failure.
        reason: String,
    },

    /// AY's solve denominator differs from the normalized official field.
    #[error(
        "AY track {track_id:?} uses solve denominator {reported}; official field requires {expected}"
    )]
    AyDenominatorMismatch {
        /// Track identifier.
        track_id: String,
        /// AY's reported denominator.
        reported: u64,
        /// Official field denominator.
        expected: u64,
    },

    /// A typed AY score could not be decoded or violates its schema.
    #[error("AY track {track_id:?} has invalid score: {reason}")]
    InvalidAyScore {
        /// Track identifier.
        track_id: String,
        /// Score parsing or range failure.
        reason: String,
    },

    /// AY's score-level solved count differs from its solve summary.
    #[error(
        "AY track {track_id:?} score says solved={score_solved}, but solve summary says solved={summary_solved}"
    )]
    AySolvedCountMismatch {
        /// Track identifier.
        track_id: String,
        /// Solved count inside the typed score.
        score_solved: u64,
        /// Solved count in the solve-rate summary.
        summary_solved: u64,
    },

    /// AY's rank is zero or outside the official eligible field plus AY.
    #[error(
        "AY track {track_id:?} has rank {rank}; expected 1..={maximum} against the official field"
    )]
    InvalidAyRank {
        /// Track identifier.
        track_id: String,
        /// Reported rank.
        rank: u64,
        /// Largest possible insertion rank.
        maximum: u64,
    },

    /// AY's reported rank disagrees with the registered comparator.
    #[error(
        "AY track {track_id:?} reports rank {reported}; registered scorer recomputes rank {expected}"
    )]
    AyScoreRankMismatch {
        /// Track identifier.
        track_id: String,
        /// Reported rank.
        reported: u64,
        /// Recomputed insertion rank.
        expected: u64,
    },

    /// AY's win flag is inconsistent with rank one.
    #[error("AY track {track_id:?} has rank {rank} and win={win}; a win must be exactly rank one")]
    AyWinMismatch {
        /// Track identifier.
        track_id: String,
        /// Reported rank.
        rank: u64,
        /// Reported win flag.
        win: bool,
    },

    /// An identity is blank or has surrounding/control whitespace.
    #[error("track {track_id:?} has invalid {field} identity {id:?}")]
    InvalidIdentity {
        /// Track identifier.
        track_id: String,
        /// Identity role.
        field: &'static str,
        /// Invalid identity.
        id: String,
    },

    /// A provenance identity that must be content-bound lacks a digest.
    #[error("track {track_id:?} {field} identity has no SHA-256 digest")]
    MissingSha256 {
        /// Track identifier.
        track_id: String,
        /// Identity role.
        field: &'static str,
    },

    /// A SHA-256 is not canonical lowercase hexadecimal.
    #[error("track {track_id:?} has invalid {field} SHA-256 {sha256:?}")]
    InvalidSha256 {
        /// Track identifier.
        track_id: String,
        /// Identity role.
        field: &'static str,
        /// Invalid digest.
        sha256: String,
    },
}

/// All validation issues found in one pass.
#[derive(Clone, Debug, PartialEq)]
pub struct CampaignValidationErrors {
    /// Individually classified issues.
    pub issues: Vec<CampaignValidationIssue>,
}

impl fmt::Display for CampaignValidationErrors {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "campaign report validation failed with {} issue(s)",
            self.issues.len()
        )?;
        for issue in &self.issues {
            write!(formatter, "; {issue}")?;
        }
        Ok(())
    }
}

impl std::error::Error for CampaignValidationErrors {}

/// Loading, parsing, or validating a campaign report failed.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CampaignError {
    /// A source document could not be read.
    #[error("failed to read {document} {path}: {source}")]
    Read {
        /// Document kind.
        document: CampaignDocument,
        /// Source path.
        path: PathBuf,
        /// I/O failure.
        #[source]
        source: std::io::Error,
    },

    /// The continuous catalog is not valid TOML for schema 1.
    #[error("failed to parse continuous catalog {path}: {source}")]
    ParseCatalog {
        /// Source path.
        path: PathBuf,
        /// TOML parse failure.
        #[source]
        source: toml::de::Error,
    },

    /// A normalized JSON report could not be decoded.
    #[error("failed to parse {document} {path}: {source}")]
    ParseJson {
        /// Document kind.
        document: CampaignDocument,
        /// Source path.
        path: PathBuf,
        /// JSON parse failure.
        #[source]
        source: serde_json::Error,
    },

    /// A declared longitudinal identity does not hash to the loaded bytes.
    #[error("{document} {path} SHA-256 mismatch: declared {declared}, actual {actual}")]
    DeclaredSha256Mismatch {
        /// Artifact whose bytes were hashed.
        document: CampaignDocument,
        /// Artifact path.
        path: PathBuf,
        /// Digest declared by the consuming report.
        declared: String,
        /// Digest of the bytes actually loaded.
        actual: String,
    },

    /// The joined documents violate one or more invariants.
    #[error(transparent)]
    Validation(#[from] CampaignValidationErrors),
}

/// Three loaded documents whose cross-document invariants have been checked.
#[derive(Clone, Debug)]
pub struct ValidatedCampaign {
    /// Validated continuous catalog.
    pub catalog: ContinuousCatalog,
    /// Validated official field.
    pub official_field: OfficialFieldReport,
    /// Validated AY score report.
    pub ay_report: AyScoreReport,
}

/// Load the continuous TOML catalog.
pub fn load_continuous_catalog(path: &Path) -> Result<ContinuousCatalog, CampaignError> {
    let text = read_document(path, CampaignDocument::Catalog)?;
    parse_catalog(&text, path)
}

fn parse_catalog(text: &str, path: &Path) -> Result<ContinuousCatalog, CampaignError> {
    toml::from_str(text).map_err(|source| CampaignError::ParseCatalog {
        path: path.to_path_buf(),
        source,
    })
}

/// Load a normalized official-field JSON document.
pub fn load_official_field(path: &Path) -> Result<OfficialFieldReport, CampaignError> {
    load_json(path, CampaignDocument::OfficialField)
}

/// Load a normalized AY score-report JSON document.
pub fn load_ay_score_report(path: &Path) -> Result<AyScoreReport, CampaignError> {
    load_json(path, CampaignDocument::AyScoreReport)
}

/// Load and validate all three campaign documents.
pub fn load_and_validate_campaign(
    catalog_path: &Path,
    official_field_path: &Path,
    ay_report_path: &Path,
) -> Result<ValidatedCampaign, CampaignError> {
    // Read each artifact exactly once so validation and hashing observe the
    // same bytes even if a producer is concurrently replacing a report.
    let catalog_text = read_document(catalog_path, CampaignDocument::Catalog)?;
    let official_field_text = read_document(official_field_path, CampaignDocument::OfficialField)?;
    let ay_report_text = read_document(ay_report_path, CampaignDocument::AyScoreReport)?;
    let catalog = parse_catalog(&catalog_text, catalog_path)?;
    let official_field = parse_json(
        &official_field_text,
        official_field_path,
        CampaignDocument::OfficialField,
    )?;
    let ay_report = parse_json(
        &ay_report_text,
        ay_report_path,
        CampaignDocument::AyScoreReport,
    )?;
    validate_campaign(&catalog, &official_field, &ay_report)?;
    validate_declared_sha256(
        CampaignDocument::Catalog,
        catalog_path,
        catalog_text.as_bytes(),
        &official_field.catalog,
    )?;
    validate_declared_sha256(
        CampaignDocument::OfficialField,
        official_field_path,
        official_field_text.as_bytes(),
        &ay_report.official_field,
    )?;
    Ok(ValidatedCampaign {
        catalog,
        official_field,
        ay_report,
    })
}

fn read_document(path: &Path, document: CampaignDocument) -> Result<String, CampaignError> {
    fs::read_to_string(path).map_err(|source| CampaignError::Read {
        document,
        path: path.to_path_buf(),
        source,
    })
}

fn load_json<T>(path: &Path, document: CampaignDocument) -> Result<T, CampaignError>
where
    T: for<'de> Deserialize<'de>,
{
    let text = read_document(path, document)?;
    parse_json(&text, path, document)
}

fn parse_json<T>(text: &str, path: &Path, document: CampaignDocument) -> Result<T, CampaignError>
where
    T: for<'de> Deserialize<'de>,
{
    serde_json::from_str(text).map_err(|source| CampaignError::ParseJson {
        document,
        path: path.to_path_buf(),
        source,
    })
}

fn validate_declared_sha256(
    document: CampaignDocument,
    path: &Path,
    bytes: &[u8],
    identity: &CampaignIdentity,
) -> Result<(), CampaignError> {
    let Some(declared) = identity.sha256.as_ref() else {
        // `validate_campaign` reports the missing required digest before this
        // byte-level check is reached.
        return Ok(());
    };
    let actual = sha256_hex(bytes);
    if *declared == actual {
        Ok(())
    } else {
        Err(CampaignError::DeclaredSha256Mismatch {
            document,
            path: path.to_path_buf(),
            declared: declared.clone(),
            actual,
        })
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// Validate schema versions, exact catalog coverage, dispositions, scores,
/// rankings, and evidence identities.
pub fn validate_campaign(
    catalog: &ContinuousCatalog,
    official_field: &OfficialFieldReport,
    ay_report: &AyScoreReport,
) -> Result<(), CampaignValidationErrors> {
    let mut issues = Vec::new();
    validate_schema_versions(catalog, official_field, ay_report, &mut issues);
    validate_report_metadata(official_field, ay_report, &mut issues);
    validate_catalog_metadata(catalog, &mut issues);

    if catalog.tracks.is_empty() {
        issues.push(CampaignValidationIssue::EmptyCatalog);
    }

    let catalog_by_id = index_catalog(&catalog.tracks, &mut issues);
    let official_by_id = index_official(&official_field.leaderboards, &catalog_by_id, &mut issues);
    let ay_by_id = index_ay(&ay_report.rows, &catalog_by_id, &mut issues);

    for (track_id, track) in &catalog_by_id {
        let expected = expected_official_dispositions(track, &mut issues);
        let official = official_by_id.get(track_id).copied();
        let ay = ay_by_id.get(track_id).copied();

        if official.is_none() {
            issues.push(CampaignValidationIssue::MissingTrackId {
                document: CampaignDocument::OfficialField,
                track_id: (*track_id).to_owned(),
            });
        }
        if ay.is_none() {
            issues.push(CampaignValidationIssue::MissingTrackId {
                document: CampaignDocument::AyScoreReport,
                track_id: (*track_id).to_owned(),
            });
        }

        if let Some(official) = official {
            if let Some((allowed, description)) = expected {
                if !allowed.contains(&official.disposition) {
                    issues.push(CampaignValidationIssue::OfficialDispositionMismatch {
                        track_id: (*track_id).to_owned(),
                        allowed: description,
                        found: official.disposition,
                    });
                }
            }
            validate_official_leaderboard(track, official, &mut issues);
        }

        if let Some(ay) = ay {
            validate_ay_row(track, ay, official, &mut issues);
        }
    }

    if issues.is_empty() {
        Ok(())
    } else {
        Err(CampaignValidationErrors { issues })
    }
}

fn validate_schema_versions(
    catalog: &ContinuousCatalog,
    official_field: &OfficialFieldReport,
    ay_report: &AyScoreReport,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    for (document, found) in [
        (CampaignDocument::Catalog, catalog.schema_version),
        (
            CampaignDocument::OfficialField,
            official_field.schema_version,
        ),
        (CampaignDocument::AyScoreReport, ay_report.schema_version),
    ] {
        if found != CAMPAIGN_SCHEMA_VERSION {
            issues.push(CampaignValidationIssue::SchemaVersion {
                document,
                found,
                expected: CAMPAIGN_SCHEMA_VERSION,
            });
        }
    }
}

fn validate_report_metadata(
    official_field: &OfficialFieldReport,
    ay_report: &AyScoreReport,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    for (document, generated_at) in [
        (
            CampaignDocument::OfficialField,
            official_field.generated_at.as_str(),
        ),
        (
            CampaignDocument::AyScoreReport,
            ay_report.generated_at.as_str(),
        ),
    ] {
        if !is_strict_utc_rfc3339(generated_at) {
            issues.push(CampaignValidationIssue::InvalidGeneratedAt {
                document,
                value: generated_at.to_owned(),
            });
        }
    }

    for (document, field, identity) in [
        (
            CampaignDocument::OfficialField,
            "catalog",
            &official_field.catalog,
        ),
        (
            CampaignDocument::AyScoreReport,
            "catalog",
            &ay_report.catalog,
        ),
        (
            CampaignDocument::AyScoreReport,
            "official_field",
            &ay_report.official_field,
        ),
    ] {
        validate_report_identity(document, field, identity, issues);
    }

    if ay_report.catalog != official_field.catalog {
        issues.push(CampaignValidationIssue::CatalogIdentityMismatch);
    }
}

fn validate_catalog_metadata(
    catalog: &ContinuousCatalog,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    if !valid_human_name(&catalog.scope) {
        issues.push(CampaignValidationIssue::InvalidCatalogScope {
            value: catalog.scope.clone(),
        });
    }
}

fn validate_report_identity(
    document: CampaignDocument,
    field: &'static str,
    identity: &CampaignIdentity,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    if !valid_human_name(&identity.id) {
        issues.push(CampaignValidationIssue::InvalidReportIdentity {
            document,
            field,
            id: identity.id.clone(),
        });
    }
    match &identity.sha256 {
        None => issues.push(CampaignValidationIssue::MissingReportSha256 { document, field }),
        Some(sha256) if !is_sha256_hex(sha256) => {
            issues.push(CampaignValidationIssue::InvalidReportSha256 {
                document,
                field,
                sha256: sha256.clone(),
            });
        }
        Some(_) => {}
    }
}

fn index_catalog<'a>(
    tracks: &'a [CatalogTrack],
    issues: &mut Vec<CampaignValidationIssue>,
) -> BTreeMap<&'a str, &'a CatalogTrack> {
    let mut by_id = BTreeMap::new();
    for track in tracks {
        validate_track_id(CampaignDocument::Catalog, &track.id, issues);
        validate_catalog_track(track, issues);
        if by_id.insert(track.id.as_str(), track).is_some() {
            issues.push(CampaignValidationIssue::DuplicateTrackId {
                document: CampaignDocument::Catalog,
                track_id: track.id.clone(),
            });
        }
    }
    by_id
}

fn validate_catalog_track(track: &CatalogTrack, issues: &mut Vec<CampaignValidationIssue>) {
    for (field, value) in [
        ("readiness", track.readiness.as_str()),
        ("official_score_kind", track.official_score_kind.as_str()),
    ] {
        if !valid_human_name(value) {
            issues.push(CampaignValidationIssue::InvalidCatalogField {
                track_id: track.id.clone(),
                field,
                value: value.to_owned(),
            });
        }
    }

    if !matches!(
        track.official_score_direction.as_str(),
        "minimize" | "maximize" | "mixed-lexicographic" | "none" | "pending"
    ) {
        issues.push(CampaignValidationIssue::UnknownOfficialScoreDirection {
            track_id: track.id.clone(),
            direction: track.official_score_direction.clone(),
        });
    }

    if !matches!(
        track.ay_adapter_status.as_str(),
        "ready" | "partial" | "unsupported" | "not-applicable"
    ) {
        issues.push(CampaignValidationIssue::UnknownAyAdapterStatus {
            track_id: track.id.clone(),
            status: track.ay_adapter_status.clone(),
        });
    }
}

fn index_official<'a>(
    leaderboards: &'a [OfficialLeaderboard],
    catalog: &BTreeMap<&str, &CatalogTrack>,
    issues: &mut Vec<CampaignValidationIssue>,
) -> BTreeMap<&'a str, &'a OfficialLeaderboard> {
    let mut by_id = BTreeMap::new();
    for leaderboard in leaderboards {
        validate_track_id(
            CampaignDocument::OfficialField,
            &leaderboard.track_id,
            issues,
        );
        if !catalog.contains_key(leaderboard.track_id.as_str()) {
            issues.push(CampaignValidationIssue::UnknownTrackId {
                document: CampaignDocument::OfficialField,
                track_id: leaderboard.track_id.clone(),
            });
        }
        if by_id
            .insert(leaderboard.track_id.as_str(), leaderboard)
            .is_some()
        {
            issues.push(CampaignValidationIssue::DuplicateTrackId {
                document: CampaignDocument::OfficialField,
                track_id: leaderboard.track_id.clone(),
            });
        }
    }
    by_id
}

fn index_ay<'a>(
    rows: &'a [AyScoreRow],
    catalog: &BTreeMap<&str, &CatalogTrack>,
    issues: &mut Vec<CampaignValidationIssue>,
) -> BTreeMap<&'a str, &'a AyScoreRow> {
    let mut by_id = BTreeMap::new();
    for row in rows {
        validate_track_id(CampaignDocument::AyScoreReport, &row.track_id, issues);
        if !catalog.contains_key(row.track_id.as_str()) {
            issues.push(CampaignValidationIssue::UnknownTrackId {
                document: CampaignDocument::AyScoreReport,
                track_id: row.track_id.clone(),
            });
        }
        if by_id.insert(row.track_id.as_str(), row).is_some() {
            issues.push(CampaignValidationIssue::DuplicateTrackId {
                document: CampaignDocument::AyScoreReport,
                track_id: row.track_id.clone(),
            });
        }
    }
    by_id
}

fn validate_track_id(
    document: CampaignDocument,
    track_id: &str,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    if !is_canonical_track_id(track_id) {
        issues.push(CampaignValidationIssue::NonCanonicalTrackId {
            document,
            track_id: track_id.to_owned(),
        });
    }
}

/// Whether an identifier is non-empty lowercase ASCII kebab case.
#[must_use]
pub fn is_canonical_track_id(track_id: &str) -> bool {
    let mut previous_hyphen = true;
    for byte in track_id.bytes() {
        match byte {
            b'a'..=b'z' | b'0'..=b'9' => previous_hyphen = false,
            b'-' if !previous_hyphen => previous_hyphen = true,
            _ => return false,
        }
    }
    !previous_hyphen
}

fn expected_official_dispositions(
    track: &CatalogTrack,
    issues: &mut Vec<CampaignValidationIssue>,
) -> Option<(&'static [ScoreDisposition], &'static str)> {
    const FINAL: &[ScoreDisposition] = &[
        ScoreDisposition::Scored,
        ScoreDisposition::Partial,
        ScoreDisposition::Unmaterialized,
        ScoreDisposition::PendingNormalization,
    ];
    const PARTIAL: &[ScoreDisposition] = &[ScoreDisposition::Partial];
    const PENDING: &[ScoreDisposition] = &[ScoreDisposition::Pending];
    const CANCELLED: &[ScoreDisposition] = &[ScoreDisposition::Cancelled];
    const NOT_HELD: &[ScoreDisposition] = &[ScoreDisposition::NotHeld];
    const NOT_RANKED: &[ScoreDisposition] = &[ScoreDisposition::NotRanked];

    let expected = match track.status.as_str() {
        "final" => (
            FINAL,
            "scored, partial, unmaterialized, or pending-normalization",
        ),
        "final-field-partial" | "provisional-field-partial" => (PARTIAL, "partial"),
        "final-field-unpublished" => (PENDING, "pending"),
        "cancelled" => (CANCELLED, "cancelled"),
        "not-held" | "omitted" => (NOT_HELD, "not-held"),
        "demo-no-separate-award"
        | "experimental-no-ranking"
        | "experimental-one-submission-no-published-ranking"
        | "final-unranked"
        | "no-medal-no-entrants" => (NOT_RANKED, "not-ranked"),
        "conditional-pending-results"
        | "conditional-unconfirmed"
        | "event-held-public-artifacts-pending"
        | "event-ran-artifacts-pending"
        | "event-running-results-pending"
        | "experimental-pending-results-aggregate-placeholder"
        | "experimental-results-unpublished"
        | "final-aggregate-placeholder"
        | "full-run-window-complete-results-pending"
        | "pending-results"
        | "pending-results-aggregate-placeholder"
        | "planned-separate-event"
        | "provisional-primary-branch-results-public"
        | "results-certified-report-pending"
        | "scheduled"
        | "scheduled-results-pending"
        | "scheduled-unranked" => (PENDING, "pending"),
        status => {
            issues.push(CampaignValidationIssue::UnknownCatalogStatus {
                track_id: track.id.clone(),
                status: status.to_owned(),
            });
            return None;
        }
    };
    Some(expected)
}

#[derive(Clone, Copy, Debug)]
enum RegisteredScoreComparator {
    AcceptableSolutionsThenAverageTime,
    AveragePar2,
    CertifiedSolvedCount,
    CorrectYesNoCount,
    CorrectCount,
    CorrectCountThenRuntime,
    MaximizeOfficialRatio,
    SolvedCountThenAverageTime,
}

impl RegisteredScoreComparator {
    fn for_track(track: &CatalogTrack, issues: &mut Vec<CampaignValidationIssue>) -> Option<Self> {
        let (comparator, expected_direction) = match track.official_score_kind.as_str() {
            "acceptable-solutions-then-average-time" => (
                Self::AcceptableSolutionsThenAverageTime,
                "mixed-lexicographic",
            ),
            "average-par2" => (Self::AveragePar2, "minimize"),
            "certified-solved-count" => (Self::CertifiedSolvedCount, "maximize"),
            "correct-yes-no-count-with-disqualification" => (Self::CorrectYesNoCount, "maximize"),
            "correct-count" => (Self::CorrectCount, "maximize"),
            "correct-count-then-runtime" => (Self::CorrectCountThenRuntime, "mixed-lexicographic"),
            "noncontradictory-answers-minus-penalties"
            | "official-complexity-category-score"
            | "official-probabilistic-category-points" => (Self::MaximizeOfficialRatio, "maximize"),
            "solved-count-then-average-time" => {
                (Self::SolvedCountThenAverageTime, "mixed-lexicographic")
            }
            _ => {
                issues.push(CampaignValidationIssue::UnsupportedScoreComparator {
                    track_id: track.id.clone(),
                    score_kind: track.official_score_kind.clone(),
                });
                return None;
            }
        };
        if track.official_score_direction != expected_direction {
            issues.push(CampaignValidationIssue::ScoreDirectionMismatch {
                track_id: track.id.clone(),
                score_kind: track.official_score_kind.clone(),
                expected: expected_direction,
                found: track.official_score_direction.clone(),
            });
        }
        Some(comparator)
    }

    fn parse(self, value: &Value) -> Result<ComparableScore, String> {
        match self {
            Self::AcceptableSolutionsThenAverageTime => {
                let score: AcceptableSolutionsThenAverageTimeScore =
                    serde_json::from_value(value.clone()).map_err(|error| error.to_string())?;
                Ok(ComparableScore::CountThenRuntime {
                    solved: score.acceptable_solutions,
                    runtime: score.average_time_centiseconds.unwrap_or(u64::MAX),
                })
            }
            Self::AveragePar2 => {
                let score: AveragePar2Score =
                    serde_json::from_value(value.clone()).map_err(|error| error.to_string())?;
                if score.average_par2_denominator == 0 {
                    return Err("average PAR-2 denominator must be nonzero".to_owned());
                }
                Ok(ComparableScore::MinimizeRatio {
                    numerator: score.average_par2_numerator,
                    denominator: score.average_par2_denominator,
                })
            }
            Self::CertifiedSolvedCount => {
                let score: CertifiedSolvedCountScore =
                    serde_json::from_value(value.clone()).map_err(|error| error.to_string())?;
                Ok(ComparableScore::CountThenRuntime {
                    solved: score.certified_solved,
                    runtime: 0,
                })
            }
            Self::CorrectYesNoCount => {
                let score: CorrectYesNoCountScore =
                    serde_json::from_value(value.clone()).map_err(|error| error.to_string())?;
                let solved = score
                    .correct_yes
                    .checked_add(score.correct_no)
                    .ok_or_else(|| "correct YES+NO count overflows u64".to_owned())?;
                Ok(ComparableScore::CountThenRuntime { solved, runtime: 0 })
            }
            Self::CorrectCount => {
                let score: CorrectCountScore =
                    serde_json::from_value(value.clone()).map_err(|error| error.to_string())?;
                Ok(ComparableScore::CountThenRuntime {
                    solved: score.correct,
                    runtime: 0,
                })
            }
            Self::CorrectCountThenRuntime => {
                let score: CorrectCountThenRuntimeScore =
                    serde_json::from_value(value.clone()).map_err(|error| error.to_string())?;
                Ok(ComparableScore::CountThenRuntime {
                    solved: score.solved,
                    runtime: score.cpu_seconds,
                })
            }
            Self::MaximizeOfficialRatio => {
                let score: OfficialRatioScore =
                    serde_json::from_value(value.clone()).map_err(|error| error.to_string())?;
                if score.official_score_denominator == 0 {
                    return Err("official score denominator must be nonzero".to_owned());
                }
                Ok(ComparableScore::MaximizeRatio {
                    numerator: score.official_score_numerator,
                    denominator: score.official_score_denominator,
                })
            }
            Self::SolvedCountThenAverageTime => {
                let score: SolvedCountThenAverageTimeScore =
                    serde_json::from_value(value.clone()).map_err(|error| error.to_string())?;
                Ok(ComparableScore::CountThenRuntime {
                    solved: score.solved,
                    runtime: score.average_time_centiseconds.unwrap_or(u64::MAX),
                })
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct AveragePar2Score {
    average_par2_numerator: u64,
    average_par2_denominator: u64,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct AcceptableSolutionsThenAverageTimeScore {
    acceptable_solutions: u64,
    average_time_centiseconds: Option<u64>,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CertifiedSolvedCountScore {
    certified_solved: u64,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CorrectYesNoCountScore {
    correct_yes: u64,
    correct_no: u64,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CorrectCountScore {
    correct: u64,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CorrectCountThenRuntimeScore {
    solved: u64,
    cpu_seconds: u64,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct OfficialRatioScore {
    official_score_numerator: u64,
    official_score_denominator: u64,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct SolvedCountThenAverageTimeScore {
    solved: u64,
    average_time_centiseconds: Option<u64>,
}

#[derive(Clone, Copy, Debug)]
enum ComparableScore {
    CountThenRuntime { solved: u64, runtime: u64 },
    MaximizeRatio { numerator: u64, denominator: u64 },
    MinimizeRatio { numerator: u64, denominator: u64 },
}

impl ComparableScore {
    /// Compare by official preference. `Greater` means `self` ranks ahead.
    fn compare(self, other: Self) -> Ordering {
        match (self, other) {
            (
                Self::CountThenRuntime {
                    solved: self_solved,
                    runtime: self_runtime,
                },
                Self::CountThenRuntime {
                    solved: other_solved,
                    runtime: other_runtime,
                },
            ) => self_solved
                .cmp(&other_solved)
                .then_with(|| other_runtime.cmp(&self_runtime)),
            (
                Self::MaximizeRatio {
                    numerator: self_numerator,
                    denominator: self_denominator,
                },
                Self::MaximizeRatio {
                    numerator: other_numerator,
                    denominator: other_denominator,
                },
            ) => {
                let self_scaled = u128::from(self_numerator) * u128::from(other_denominator);
                let other_scaled = u128::from(other_numerator) * u128::from(self_denominator);
                self_scaled.cmp(&other_scaled)
            }
            (
                Self::MinimizeRatio {
                    numerator: self_numerator,
                    denominator: self_denominator,
                },
                Self::MinimizeRatio {
                    numerator: other_numerator,
                    denominator: other_denominator,
                },
            ) => {
                let self_scaled = u128::from(self_numerator) * u128::from(other_denominator);
                let other_scaled = u128::from(other_numerator) * u128::from(self_denominator);
                other_scaled.cmp(&self_scaled)
            }
            _ => {
                debug_assert!(
                    false,
                    "a track compared scores from different comparator families"
                );
                Ordering::Equal
            }
        }
    }

    fn solved_count(self) -> Option<u64> {
        match self {
            Self::CountThenRuntime { solved, .. } => Some(solved),
            Self::MaximizeRatio { .. } | Self::MinimizeRatio { .. } => None,
        }
    }
}

fn validate_official_score_ranking(
    track: &CatalogTrack,
    leaderboard: &OfficialLeaderboard,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    let Some(comparator) = RegisteredScoreComparator::for_track(track, issues) else {
        return;
    };
    let denominator = leaderboard.denominator.filter(|value| *value > 0);
    let mut scores = Vec::with_capacity(leaderboard.competitors.len());
    for competitor in &leaderboard.competitors {
        if !competitor.eligible {
            issues.push(CampaignValidationIssue::UnsupportedScoredEligibility {
                track_id: leaderboard.track_id.clone(),
                name: competitor.name.clone(),
            });
        }
        let parsed = comparator.parse(&competitor.score);
        match parsed {
            Ok(score) => {
                if let (Some(total), Some(solved)) = (denominator, score.solved_count()) {
                    if solved > total {
                        issues.push(CampaignValidationIssue::InvalidOfficialScore {
                            track_id: leaderboard.track_id.clone(),
                            name: competitor.name.clone(),
                            reason: format!("solved={solved} exceeds denominator={total}"),
                        });
                        scores.push(None);
                        continue;
                    }
                }
                scores.push(Some(score));
            }
            Err(reason) => {
                issues.push(CampaignValidationIssue::InvalidOfficialScore {
                    track_id: leaderboard.track_id.clone(),
                    name: competitor.name.clone(),
                    reason,
                });
                scores.push(None);
            }
        }
    }

    for (index, competitor) in leaderboard.competitors.iter().enumerate() {
        let Some(score) = scores[index] else {
            continue;
        };
        let better = scores
            .iter()
            .flatten()
            .filter(|other| other.compare(score) == Ordering::Greater)
            .count() as u64;
        let expected = better.saturating_add(1);
        if competitor.rank != expected {
            issues.push(CampaignValidationIssue::OfficialScoreRankMismatch {
                track_id: leaderboard.track_id.clone(),
                name: competitor.name.clone(),
                reported: competitor.rank,
                expected,
            });
        }
    }
}

fn validate_official_leaderboard(
    track: &CatalogTrack,
    leaderboard: &OfficialLeaderboard,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    for evidence in &leaderboard.evidence {
        validate_identity(
            &leaderboard.track_id,
            "official evidence",
            evidence,
            IdentityDigest::Required,
            issues,
        );
    }

    if !leaderboard.disposition.has_published_field() {
        if leaderboard.denominator.is_some() {
            issues.push(CampaignValidationIssue::OfficialDenominatorForbidden {
                track_id: leaderboard.track_id.clone(),
                disposition: leaderboard.disposition,
            });
        }
        if !leaderboard.competitors.is_empty() {
            issues.push(CampaignValidationIssue::CompetitorsForbidden {
                track_id: leaderboard.track_id.clone(),
                disposition: leaderboard.disposition,
            });
        }
        if leaderboard.disposition == ScoreDisposition::PendingNormalization
            && !leaderboard.evidence.is_empty()
        {
            issues.push(CampaignValidationIssue::OfficialEvidenceForbidden {
                track_id: leaderboard.track_id.clone(),
                disposition: leaderboard.disposition,
            });
        }
        if leaderboard.disposition == ScoreDisposition::Unmaterialized
            && leaderboard.evidence.is_empty()
        {
            issues.push(CampaignValidationIssue::MissingOfficialEvidence {
                track_id: leaderboard.track_id.clone(),
            });
        }
        return;
    }

    match leaderboard.denominator {
        Some(0) => issues.push(CampaignValidationIssue::InvalidOfficialDenominator {
            track_id: leaderboard.track_id.clone(),
            denominator: 0,
        }),
        None if leaderboard.disposition == ScoreDisposition::Scored => {
            issues.push(CampaignValidationIssue::MissingOfficialDenominator {
                track_id: leaderboard.track_id.clone(),
            });
        }
        Some(_) | None => {}
    }

    if leaderboard.competitors.is_empty() {
        issues.push(CampaignValidationIssue::EmptyOfficialField {
            track_id: leaderboard.track_id.clone(),
        });
    }
    if leaderboard.evidence.is_empty() {
        issues.push(CampaignValidationIssue::MissingOfficialEvidence {
            track_id: leaderboard.track_id.clone(),
        });
    }

    let mut names = HashSet::new();
    let mut ranks: BTreeMap<u64, Vec<&OfficialCompetitor>> = BTreeMap::new();
    for competitor in &leaderboard.competitors {
        if !valid_human_name(&competitor.name) {
            issues.push(CampaignValidationIssue::InvalidCompetitorName {
                track_id: leaderboard.track_id.clone(),
                name: competitor.name.clone(),
            });
        }
        if !names.insert(competitor.name.as_str()) {
            issues.push(CampaignValidationIssue::DuplicateCompetitorName {
                track_id: leaderboard.track_id.clone(),
                name: competitor.name.clone(),
            });
        }
        if competitor.rank == 0 {
            issues.push(CampaignValidationIssue::InvalidCompetitorRank {
                track_id: leaderboard.track_id.clone(),
                name: competitor.name.clone(),
            });
        }
        if leaderboard.disposition == ScoreDisposition::Scored && competitor.score.is_null() {
            issues.push(CampaignValidationIssue::MissingOfficialScore {
                track_id: leaderboard.track_id.clone(),
                name: competitor.name.clone(),
            });
        }
        ranks.entry(competitor.rank).or_default().push(competitor);
    }

    let mut expected_rank = 1_u64;
    for (rank, group) in &ranks {
        if *rank != expected_rank {
            issues.push(CampaignValidationIssue::InvalidCompetitionRankSequence {
                track_id: leaderboard.track_id.clone(),
                expected: expected_rank,
                found: *rank,
            });
        }
        if group.len() > 1 && group.iter().any(|competitor| !competitor.tied) {
            issues.push(CampaignValidationIssue::RankTieNotExplicit {
                track_id: leaderboard.track_id.clone(),
                rank: *rank,
            });
        } else if group.len() == 1 && group[0].tied {
            issues.push(CampaignValidationIssue::SpuriousRankTie {
                track_id: leaderboard.track_id.clone(),
                rank: *rank,
            });
        }
        expected_rank = rank.saturating_add(group.len() as u64);
    }

    let best_eligible_rank = leaderboard
        .competitors
        .iter()
        .filter(|competitor| competitor.eligible && competitor.rank > 0)
        .map(|competitor| competitor.rank)
        .min();
    if best_eligible_rank != Some(1) {
        issues.push(CampaignValidationIssue::NoEligibleCompetitor {
            track_id: leaderboard.track_id.clone(),
        });
    }
    for competitor in &leaderboard.competitors {
        let expected = competitor.eligible && competitor.rank == 1;
        if competitor.winner != expected {
            issues.push(CampaignValidationIssue::OfficialWinnerMismatch {
                track_id: leaderboard.track_id.clone(),
                name: competitor.name.clone(),
                expected,
            });
        }
    }

    if leaderboard.disposition == ScoreDisposition::Scored {
        validate_official_score_ranking(track, leaderboard, issues);
    }
}

fn validate_ay_row(
    track: &CatalogTrack,
    row: &AyScoreRow,
    official: Option<&OfficialLeaderboard>,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    let digest_requirement = if row.disposition == ScoreDisposition::Scored {
        IdentityDigest::Required
    } else {
        IdentityDigest::Optional
    };
    for (field, identity) in [
        ("candidate", row.candidate.as_ref()),
        ("corpus", row.corpus.as_ref()),
        ("scorer", row.scorer.as_ref()),
        ("checker", row.checker.as_ref()),
        ("envelope", row.envelope.as_ref()),
    ] {
        if let Some(identity) = identity {
            validate_identity(&row.track_id, field, identity, digest_requirement, issues);
        }
    }
    for evidence in &row.evidence {
        validate_identity(
            &row.track_id,
            "evidence",
            evidence,
            digest_requirement,
            issues,
        );
    }

    if let Some(official) = official {
        let compatible = match official.disposition {
            ScoreDisposition::Scored => matches!(
                row.disposition,
                ScoreDisposition::Scored
                    | ScoreDisposition::Pending
                    | ScoreDisposition::Unsupported
            ),
            ScoreDisposition::Partial => matches!(
                row.disposition,
                ScoreDisposition::Pending | ScoreDisposition::Unsupported
            ),
            ScoreDisposition::Unmaterialized => matches!(
                row.disposition,
                ScoreDisposition::Pending | ScoreDisposition::Unsupported
            ),
            ScoreDisposition::PendingNormalization => matches!(
                row.disposition,
                ScoreDisposition::Pending | ScoreDisposition::Unsupported
            ),
            disposition => row.disposition == disposition,
        };
        if !compatible {
            issues.push(CampaignValidationIssue::AyDispositionMismatch {
                track_id: row.track_id.clone(),
                official: official.disposition,
                found: row.disposition,
            });
        }
    }

    if row.disposition == ScoreDisposition::Scored && track.ay_adapter_status != "ready" {
        issues.push(CampaignValidationIssue::AyAdapterNotReady {
            track_id: row.track_id.clone(),
            adapter_status: track.ay_adapter_status.clone(),
        });
    }

    if !row.disposition.allows_ay_score() {
        for (field, present) in [
            ("score", row.score.is_some()),
            ("solves", row.solves.is_some()),
            ("rank", row.rank.is_some()),
            ("win", row.win.is_some()),
        ] {
            if present {
                issues.push(CampaignValidationIssue::AyClaimForbidden {
                    track_id: row.track_id.clone(),
                    disposition: row.disposition,
                    field,
                });
            }
        }
        return;
    }

    if row.score.as_ref().is_none_or(Value::is_null) {
        missing_ay_field(row, "score", issues);
    }
    let Some(solves) = row.solves.as_ref() else {
        missing_ay_field(row, "solves", issues);
        require_scored_identities(row, issues);
        validate_ay_rank_and_win(track, row, official, issues);
        return;
    };
    validate_solve_summary(&row.track_id, solves, issues);
    if let Some(official) = official {
        if let Some(expected) = official.denominator {
            if solves.total != expected {
                issues.push(CampaignValidationIssue::AyDenominatorMismatch {
                    track_id: row.track_id.clone(),
                    reported: solves.total,
                    expected,
                });
            }
        }
    }
    require_scored_identities(row, issues);
    validate_ay_score_solved_count(track, row, solves, issues);
    validate_ay_rank_and_win(track, row, official, issues);
}

fn require_scored_identities(row: &AyScoreRow, issues: &mut Vec<CampaignValidationIssue>) {
    for (field, missing) in [
        ("candidate", row.candidate.is_none()),
        ("corpus", row.corpus.is_none()),
        ("scorer", row.scorer.is_none()),
        ("checker", row.checker.is_none()),
        ("envelope", row.envelope.is_none()),
        ("evidence", row.evidence.is_empty()),
    ] {
        if missing {
            missing_ay_field(row, field, issues);
        }
    }
}

fn validate_ay_rank_and_win(
    track: &CatalogTrack,
    row: &AyScoreRow,
    official: Option<&OfficialLeaderboard>,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    let Some(rank) = row.rank else {
        missing_ay_field(row, "rank", issues);
        if row.win.is_none() {
            missing_ay_field(row, "win", issues);
        }
        return;
    };
    let Some(win) = row.win else {
        missing_ay_field(row, "win", issues);
        return;
    };

    let eligible_count = official
        .filter(|leaderboard| leaderboard.disposition == ScoreDisposition::Scored)
        .map(|leaderboard| {
            leaderboard
                .competitors
                .iter()
                .filter(|competitor| competitor.eligible)
                .count() as u64
        })
        .unwrap_or(0);
    let maximum = eligible_count.saturating_add(1);
    if rank == 0 || rank > maximum {
        issues.push(CampaignValidationIssue::InvalidAyRank {
            track_id: row.track_id.clone(),
            rank,
            maximum,
        });
    }

    let recomputed_rank = recompute_ay_rank(track, row, official, issues);
    if let Some(expected) = recomputed_rank {
        if rank != expected {
            issues.push(CampaignValidationIssue::AyScoreRankMismatch {
                track_id: row.track_id.clone(),
                reported: rank,
                expected,
            });
        }
    }
    let decisive_rank = recomputed_rank.unwrap_or(rank);
    if win != (decisive_rank == 1) {
        issues.push(CampaignValidationIssue::AyWinMismatch {
            track_id: row.track_id.clone(),
            rank: decisive_rank,
            win,
        });
    }
}

fn validate_ay_score_solved_count(
    track: &CatalogTrack,
    row: &AyScoreRow,
    solves: &SolveSummary,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    let Some(score) = row.score.as_ref() else {
        return;
    };
    let Some(comparator) = registered_comparator_without_issue(track) else {
        return;
    };
    match comparator.parse(score) {
        Ok(score) => {
            if let Some(score_solved) = score.solved_count() {
                if score_solved != solves.solved {
                    issues.push(CampaignValidationIssue::AySolvedCountMismatch {
                        track_id: row.track_id.clone(),
                        score_solved,
                        summary_solved: solves.solved,
                    });
                }
            }
        }
        Err(reason) => issues.push(CampaignValidationIssue::InvalidAyScore {
            track_id: row.track_id.clone(),
            reason,
        }),
    }
}

fn recompute_ay_rank(
    track: &CatalogTrack,
    row: &AyScoreRow,
    official: Option<&OfficialLeaderboard>,
    issues: &mut Vec<CampaignValidationIssue>,
) -> Option<u64> {
    let official =
        official.filter(|leaderboard| leaderboard.disposition == ScoreDisposition::Scored)?;
    let comparator = registered_comparator_without_issue(track)?;
    let ay_value = match comparator.parse(row.score.as_ref()?) {
        Ok(value) => value,
        Err(_) => return None,
    };
    let mut better = 0_u64;
    for competitor in official
        .competitors
        .iter()
        .filter(|competitor| competitor.eligible)
    {
        let official_value = match comparator.parse(&competitor.score) {
            Ok(value) => value,
            Err(reason) => {
                issues.push(CampaignValidationIssue::InvalidOfficialScore {
                    track_id: official.track_id.clone(),
                    name: competitor.name.clone(),
                    reason,
                });
                return None;
            }
        };
        if official_value.compare(ay_value) == Ordering::Greater {
            better = better.saturating_add(1);
        }
    }
    Some(better.saturating_add(1))
}

fn registered_comparator_without_issue(track: &CatalogTrack) -> Option<RegisteredScoreComparator> {
    match track.official_score_kind.as_str() {
        "acceptable-solutions-then-average-time" => {
            Some(RegisteredScoreComparator::AcceptableSolutionsThenAverageTime)
        }
        "average-par2" => Some(RegisteredScoreComparator::AveragePar2),
        "certified-solved-count" => Some(RegisteredScoreComparator::CertifiedSolvedCount),
        "correct-yes-no-count-with-disqualification" => {
            Some(RegisteredScoreComparator::CorrectYesNoCount)
        }
        "correct-count" => Some(RegisteredScoreComparator::CorrectCount),
        "correct-count-then-runtime" => Some(RegisteredScoreComparator::CorrectCountThenRuntime),
        "noncontradictory-answers-minus-penalties"
        | "official-complexity-category-score"
        | "official-probabilistic-category-points" => {
            Some(RegisteredScoreComparator::MaximizeOfficialRatio)
        }
        "solved-count-then-average-time" => {
            Some(RegisteredScoreComparator::SolvedCountThenAverageTime)
        }
        _ => None,
    }
}

fn missing_ay_field(
    row: &AyScoreRow,
    field: &'static str,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    issues.push(CampaignValidationIssue::MissingAyScoredField {
        track_id: row.track_id.clone(),
        field,
    });
}

fn validate_solve_summary(
    track_id: &str,
    solves: &SolveSummary,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    if solves.total == 0 {
        issues.push(CampaignValidationIssue::InvalidSolveSummary {
            track_id: track_id.to_owned(),
            reason: "total must be greater than zero for a scored row".to_owned(),
        });
        return;
    }
    if solves.solved > solves.total {
        issues.push(CampaignValidationIssue::InvalidSolveSummary {
            track_id: track_id.to_owned(),
            reason: format!("solved={} exceeds total={}", solves.solved, solves.total),
        });
        return;
    }
    if !solves.solve_rate.is_finite() || !(0.0..=1.0).contains(&solves.solve_rate) {
        issues.push(CampaignValidationIssue::InvalidSolveSummary {
            track_id: track_id.to_owned(),
            reason: format!("solve_rate={} is outside [0, 1]", solves.solve_rate),
        });
        return;
    }
    let expected = solves.solved as f64 / solves.total as f64;
    if (solves.solve_rate - expected).abs() > 1e-12 {
        issues.push(CampaignValidationIssue::InvalidSolveSummary {
            track_id: track_id.to_owned(),
            reason: format!(
                "solve_rate={} does not equal solved/total={expected}",
                solves.solve_rate
            ),
        });
    }
}

#[derive(Clone, Copy)]
enum IdentityDigest {
    Optional,
    Required,
}

fn validate_identity(
    track_id: &str,
    field: &'static str,
    identity: &CampaignIdentity,
    digest: IdentityDigest,
    issues: &mut Vec<CampaignValidationIssue>,
) {
    if !valid_human_name(&identity.id) {
        issues.push(CampaignValidationIssue::InvalidIdentity {
            track_id: track_id.to_owned(),
            field,
            id: identity.id.clone(),
        });
    }
    match &identity.sha256 {
        None if matches!(digest, IdentityDigest::Required) => {
            issues.push(CampaignValidationIssue::MissingSha256 {
                track_id: track_id.to_owned(),
                field,
            });
        }
        Some(sha256) if !is_sha256_hex(sha256) => {
            issues.push(CampaignValidationIssue::InvalidSha256 {
                track_id: track_id.to_owned(),
                field,
                sha256: sha256.clone(),
            });
        }
        None | Some(_) => {}
    }
}

fn is_strict_utc_rfc3339(value: &str) -> bool {
    let bytes = value.as_bytes();
    if bytes.len() != 20
        || bytes[4] != b'-'
        || bytes[7] != b'-'
        || bytes[10] != b'T'
        || bytes[13] != b':'
        || bytes[16] != b':'
        || bytes[19] != b'Z'
    {
        return false;
    }
    for index in [0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18] {
        if !bytes[index].is_ascii_digit() {
            return false;
        }
    }

    let year = decimal_component(bytes, 0, 4);
    let month = decimal_component(bytes, 5, 7);
    let day = decimal_component(bytes, 8, 10);
    let hour = decimal_component(bytes, 11, 13);
    let minute = decimal_component(bytes, 14, 16);
    let second = decimal_component(bytes, 17, 19);
    let Some(days_in_month) = days_in_month(year, month) else {
        return false;
    };

    year > 0 && (1..=days_in_month).contains(&day) && hour <= 23 && minute <= 59 && second <= 59
}

fn decimal_component(bytes: &[u8], start: usize, end: usize) -> u32 {
    bytes[start..end]
        .iter()
        .fold(0_u32, |value, byte| value * 10 + u32::from(byte - b'0'))
}

fn days_in_month(year: u32, month: u32) -> Option<u32> {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => Some(31),
        4 | 6 | 9 | 11 => Some(30),
        2 if year.is_multiple_of(400) || (year.is_multiple_of(4) && !year.is_multiple_of(100)) => {
            Some(29)
        }
        2 => Some(28),
        _ => None,
    }
}

fn is_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn valid_human_name(value: &str) -> bool {
    !value.is_empty() && value.trim() == value && !value.chars().any(char::is_control)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    const TRACK_ID: &str = "examplecomp-2025-main";

    fn identity(id: &str) -> CampaignIdentity {
        CampaignIdentity {
            id: id.to_owned(),
            sha256: Some("a".repeat(64)),
        }
    }

    fn competitor(rank: u64, name: &str, winner: bool) -> OfficialCompetitor {
        OfficialCompetitor {
            rank,
            name: name.to_owned(),
            eligible: true,
            winner,
            tied: false,
            score: json!({
                "solved": 10 - rank,
                "cpu_seconds": rank * 100,
            }),
            metrics: json!({"solved": 10 - rank}),
        }
    }

    fn valid_bundle() -> (ContinuousCatalog, OfficialFieldReport, AyScoreReport) {
        let catalog_identity = identity("continuous-catalog-v1");
        (
            ContinuousCatalog {
                schema_version: CAMPAIGN_SCHEMA_VERSION,
                scope: "bounded-test-inventory".to_owned(),
                tracks: vec![CatalogTrack {
                    id: TRACK_ID.to_owned(),
                    status: "final".to_owned(),
                    readiness: "ready".to_owned(),
                    official_score_kind: "correct-count-then-runtime".to_owned(),
                    official_score_direction: "mixed-lexicographic".to_owned(),
                    ay_adapter_status: "ready".to_owned(),
                }],
            },
            OfficialFieldReport {
                schema_version: CAMPAIGN_SCHEMA_VERSION,
                generated_at: "2026-07-23T12:00:00Z".to_owned(),
                catalog: catalog_identity.clone(),
                leaderboards: vec![OfficialLeaderboard {
                    track_id: TRACK_ID.to_owned(),
                    disposition: ScoreDisposition::Scored,
                    competitors: vec![
                        competitor(1, "Reference Winner", true),
                        competitor(2, "Reference Runner-up", false),
                    ],
                    denominator: Some(10),
                    evidence: vec![identity("official-results-v1")],
                }],
            },
            AyScoreReport {
                schema_version: CAMPAIGN_SCHEMA_VERSION,
                generated_at: "2026-07-23T12:01:00Z".to_owned(),
                catalog: catalog_identity,
                official_field: identity("official-field-v1"),
                rows: vec![AyScoreRow {
                    track_id: TRACK_ID.to_owned(),
                    disposition: ScoreDisposition::Scored,
                    score: Some(json!({"solved": 8, "cpu_seconds": 150})),
                    solves: Some(SolveSummary {
                        solved: 8,
                        total: 10,
                        solve_rate: 0.8,
                    }),
                    rank: Some(2),
                    win: Some(false),
                    candidate: Some(identity("candidate-commit-and-binary")),
                    corpus: Some(identity("official-selection")),
                    scorer: Some(identity("official-scorer-v1")),
                    checker: Some(identity("checker-packet-v1")),
                    envelope: Some(identity("resource-envelope-v1")),
                    evidence: vec![identity("ay-run-record-v1")],
                }],
            },
        )
    }

    fn validation_issues(
        catalog: &ContinuousCatalog,
        official: &OfficialFieldReport,
        ay: &AyScoreReport,
    ) -> Vec<CampaignValidationIssue> {
        validate_campaign(catalog, official, ay)
            .expect_err("fixture must fail closed")
            .issues
    }

    fn write_hash_bound_bundle(
        corrupt_catalog_hash: bool,
        corrupt_official_hash: bool,
    ) -> (tempfile::TempDir, PathBuf, PathBuf, PathBuf) {
        let (catalog, mut official, mut ay) = valid_bundle();
        let directory = tempfile::tempdir().expect("temporary directory");
        let catalog_path = directory.path().join("catalog.toml");
        let official_path = directory.path().join("official.json");
        let ay_path = directory.path().join("ay.json");
        let catalog_text = toml::to_string(&catalog).expect("serialize catalog");
        official.catalog.sha256 = Some(if corrupt_catalog_hash {
            "b".repeat(64)
        } else {
            sha256_hex(catalog_text.as_bytes())
        });
        ay.catalog = official.catalog.clone();
        let official_text = serde_json::to_string(&official).expect("serialize official field");
        ay.official_field.sha256 = Some(if corrupt_official_hash {
            "c".repeat(64)
        } else {
            sha256_hex(official_text.as_bytes())
        });
        let ay_text = serde_json::to_string(&ay).expect("serialize AY report");
        fs::write(&catalog_path, catalog_text).expect("write catalog");
        fs::write(&official_path, official_text).expect("write official field");
        fs::write(&ay_path, ay_text).expect("write AY report");
        (directory, catalog_path, official_path, ay_path)
    }

    #[test]
    fn valid_scored_bundle_and_file_loaders_pass() {
        let (catalog, official, ay) = valid_bundle();
        validate_campaign(&catalog, &official, &ay).expect("valid campaign");

        let (_directory, catalog_path, official_path, ay_path) =
            write_hash_bound_bundle(false, false);
        let loaded = load_and_validate_campaign(&catalog_path, &official_path, &ay_path)
            .expect("load valid campaign");
        assert_eq!(loaded.catalog.tracks.len(), 1);
        assert_eq!(loaded.official_field.leaderboards.len(), 1);
        assert_eq!(loaded.ay_report.rows.len(), 1);
    }

    #[test]
    fn repository_catalog_parses_with_canonical_ids_and_known_statuses() {
        let catalog: ContinuousCatalog = toml::from_str(include_str!(
            "../../../benchmarks/continuous-2025-2026.toml"
        ))
        .expect("repository competition catalog");
        assert_eq!(catalog.schema_version, CAMPAIGN_SCHEMA_VERSION);
        assert!(!catalog.tracks.is_empty());

        let mut issues = Vec::new();
        let indexed = index_catalog(&catalog.tracks, &mut issues);
        for track in indexed.values() {
            assert!(expected_official_dispositions(track, &mut issues).is_some());
        }
        assert!(issues.is_empty(), "{issues:#?}");
    }

    #[test]
    fn catalog_scope_score_contract_and_adapter_vocabulary_are_validated() {
        let (mut catalog, official, ay) = valid_bundle();
        catalog.scope = " padded ".to_owned();
        catalog.tracks[0].readiness.clear();
        catalog.tracks[0].official_score_kind = " padded ".to_owned();
        catalog.tracks[0].official_score_direction = "sideways".to_owned();
        catalog.tracks[0].ay_adapter_status = "almost".to_owned();
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::InvalidCatalogScope { .. })));
        for field in ["readiness", "official_score_kind"] {
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::InvalidCatalogField {
                    field: found,
                    ..
                } if *found == field
            )));
        }
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::UnknownOfficialScoreDirection { .. }
        )));
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::UnknownAyAdapterStatus { .. }
        )));
    }

    #[test]
    fn every_document_requires_schema_version_one() {
        for document in [
            CampaignDocument::Catalog,
            CampaignDocument::OfficialField,
            CampaignDocument::AyScoreReport,
        ] {
            let (mut catalog, mut official, mut ay) = valid_bundle();
            match document {
                CampaignDocument::Catalog => catalog.schema_version = 2,
                CampaignDocument::OfficialField => official.schema_version = 2,
                CampaignDocument::AyScoreReport => ay.schema_version = 2,
            }
            let issues = validation_issues(&catalog, &official, &ay);
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::SchemaVersion {
                    document: found,
                    ..
                } if *found == document
            )));
        }
    }

    #[test]
    fn longitudinal_metadata_requires_valid_exact_identities() {
        let (catalog, mut official, mut ay) = valid_bundle();
        official.generated_at = " generated later ".to_owned();
        official.catalog.id = String::new();
        official.catalog.sha256 = None;
        ay.generated_at = String::new();
        ay.catalog = identity("different-catalog");
        ay.official_field.sha256 = Some("INVALID".to_owned());
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::InvalidGeneratedAt {
                document: CampaignDocument::OfficialField,
                ..
            }
        )));
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::InvalidGeneratedAt {
                document: CampaignDocument::AyScoreReport,
                ..
            }
        )));
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::InvalidReportIdentity {
                document: CampaignDocument::OfficialField,
                field: "catalog",
                ..
            }
        )));
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::MissingReportSha256 {
                document: CampaignDocument::OfficialField,
                field: "catalog",
            }
        )));
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::InvalidReportSha256 {
                document: CampaignDocument::AyScoreReport,
                field: "official_field",
                ..
            }
        )));
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::CatalogIdentityMismatch)));
    }

    #[test]
    fn generated_at_requires_exact_valid_second_resolution_utc() {
        let valid = [
            "2024-02-29T00:00:00Z",
            "2026-07-23T23:59:59Z",
            "2000-02-29T12:34:56Z",
        ];
        for generated_at in valid {
            assert!(is_strict_utc_rfc3339(generated_at), "{generated_at}");
        }
        let invalid = [
            "",
            "2026-07-23",
            "2026-07-23T12:00:00+00:00",
            "2026-07-23T12:00:00.000Z",
            "2026-7-23T12:00:00Z",
            "2026-02-29T12:00:00Z",
            "2100-02-29T12:00:00Z",
            "2026-13-01T12:00:00Z",
            "2026-04-31T12:00:00Z",
            "2026-07-23T24:00:00Z",
            "2026-07-23T12:60:00Z",
            "2026-07-23T12:00:60Z",
        ];
        for generated_at in invalid {
            assert!(!is_strict_utc_rfc3339(generated_at), "{generated_at}");
            let (catalog, mut official, ay) = valid_bundle();
            official.generated_at = generated_at.to_owned();
            let issues = validation_issues(&catalog, &official, &ay);
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::InvalidGeneratedAt {
                    document: CampaignDocument::OfficialField,
                    ..
                }
            )));
        }
    }

    #[test]
    fn loader_rejects_declared_catalog_or_official_field_hash_drift() {
        let (_directory, catalog_path, official_path, ay_path) =
            write_hash_bound_bundle(true, false);
        let error = load_and_validate_campaign(&catalog_path, &official_path, &ay_path)
            .expect_err("catalog hash drift");
        assert!(matches!(
            error,
            CampaignError::DeclaredSha256Mismatch {
                document: CampaignDocument::Catalog,
                ..
            }
        ));

        let (_directory, catalog_path, official_path, ay_path) =
            write_hash_bound_bundle(false, true);
        let error = load_and_validate_campaign(&catalog_path, &official_path, &ay_path)
            .expect_err("official-field hash drift");
        assert!(matches!(
            error,
            CampaignError::DeclaredSha256Mismatch {
                document: CampaignDocument::OfficialField,
                ..
            }
        ));
    }

    #[test]
    fn track_ids_must_be_canonical_in_every_document() {
        assert!(is_canonical_track_id("satcomp-2025-main"));
        for invalid in ["", "-main", "main-", "main--sat", "Main", "main_sat"] {
            assert!(!is_canonical_track_id(invalid), "{invalid:?}");
        }

        for document in [
            CampaignDocument::Catalog,
            CampaignDocument::OfficialField,
            CampaignDocument::AyScoreReport,
        ] {
            let (mut catalog, mut official, mut ay) = valid_bundle();
            match document {
                CampaignDocument::Catalog => catalog.tracks[0].id = "Bad_ID".to_owned(),
                CampaignDocument::OfficialField => {
                    official.leaderboards[0].track_id = "Bad_ID".to_owned();
                }
                CampaignDocument::AyScoreReport => {
                    ay.rows[0].track_id = "Bad_ID".to_owned();
                }
            }
            let issues = validation_issues(&catalog, &official, &ay);
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::NonCanonicalTrackId {
                    document: found,
                    ..
                } if *found == document
            )));
        }
    }

    #[test]
    fn duplicate_rows_fail_in_every_document() {
        for document in [
            CampaignDocument::Catalog,
            CampaignDocument::OfficialField,
            CampaignDocument::AyScoreReport,
        ] {
            let (mut catalog, mut official, mut ay) = valid_bundle();
            match document {
                CampaignDocument::Catalog => catalog.tracks.push(catalog.tracks[0].clone()),
                CampaignDocument::OfficialField => {
                    official.leaderboards.push(official.leaderboards[0].clone());
                }
                CampaignDocument::AyScoreReport => ay.rows.push(ay.rows[0].clone()),
            }
            let issues = validation_issues(&catalog, &official, &ay);
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::DuplicateTrackId {
                    document: found,
                    ..
                } if *found == document
            )));
        }
    }

    #[test]
    fn official_and_ay_rows_require_exact_catalog_coverage() {
        for document in [
            CampaignDocument::OfficialField,
            CampaignDocument::AyScoreReport,
        ] {
            let (catalog, mut official, mut ay) = valid_bundle();
            match document {
                CampaignDocument::OfficialField => official.leaderboards.clear(),
                CampaignDocument::AyScoreReport => ay.rows.clear(),
                CampaignDocument::Catalog => unreachable!(),
            }
            let issues = validation_issues(&catalog, &official, &ay);
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::MissingTrackId {
                    document: found,
                    ..
                } if *found == document
            )));
        }

        for document in [
            CampaignDocument::OfficialField,
            CampaignDocument::AyScoreReport,
        ] {
            let (catalog, mut official, mut ay) = valid_bundle();
            match document {
                CampaignDocument::OfficialField => {
                    let mut unknown = official.leaderboards[0].clone();
                    unknown.track_id = "unknown-2025-track".to_owned();
                    official.leaderboards.push(unknown);
                }
                CampaignDocument::AyScoreReport => {
                    let mut unknown = ay.rows[0].clone();
                    unknown.track_id = "unknown-2025-track".to_owned();
                    ay.rows.push(unknown);
                }
                CampaignDocument::Catalog => unreachable!(),
            }
            let issues = validation_issues(&catalog, &official, &ay);
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::UnknownTrackId {
                    document: found,
                    ..
                } if *found == document
            )));
        }
    }

    #[test]
    fn catalog_status_controls_official_disposition() {
        let cases = [
            ("final", ScoreDisposition::Scored),
            ("final-field-unpublished", ScoreDisposition::Pending),
            ("pending-results", ScoreDisposition::Pending),
            ("cancelled", ScoreDisposition::Cancelled),
            ("not-held", ScoreDisposition::NotHeld),
            ("experimental-no-ranking", ScoreDisposition::NotRanked),
        ];
        for (status, disposition) in cases {
            let (mut catalog, mut official, mut ay) = valid_bundle();
            catalog.tracks[0].status = status.to_owned();
            official.leaderboards[0].disposition = disposition;
            ay.rows[0].disposition = disposition;
            if disposition != ScoreDisposition::Scored {
                official.leaderboards[0].competitors.clear();
                official.leaderboards[0].denominator = None;
                official.leaderboards[0].evidence.clear();
                clear_ay_claims(&mut ay.rows[0]);
            }
            validate_campaign(&catalog, &official, &ay).expect("matching disposition");

            official.leaderboards[0].disposition = ScoreDisposition::Unsupported;
            let issues = validation_issues(&catalog, &official, &ay);
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::OfficialDispositionMismatch { .. }
            )));
        }

        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].status = "provisional-field-partial".to_owned();
        official.leaderboards[0].disposition = ScoreDisposition::Partial;
        official.leaderboards[0].denominator = None;
        ay.rows[0].disposition = ScoreDisposition::Pending;
        clear_ay_claims(&mut ay.rows[0]);
        validate_campaign(&catalog, &official, &ay)
            .expect("provisional partial field with pending AY result");

        let (mut catalog, official, ay) = valid_bundle();
        catalog.tracks[0].status = "new-unreviewed-status".to_owned();
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::UnknownCatalogStatus { .. })));
    }

    #[test]
    fn final_catalog_accepts_frozen_or_pending_normalization_but_not_pending() {
        let (catalog, official, ay) = valid_bundle();
        validate_campaign(&catalog, &official, &ay).expect("complete final field");

        let (catalog, mut official, mut ay) = valid_bundle();
        official.leaderboards[0].disposition = ScoreDisposition::Partial;
        ay.rows[0].disposition = ScoreDisposition::Pending;
        clear_ay_claims(&mut ay.rows[0]);
        validate_campaign(&catalog, &official, &ay).expect("partial final field");

        official.leaderboards[0].disposition = ScoreDisposition::Unmaterialized;
        official.leaderboards[0].competitors.clear();
        official.leaderboards[0].denominator = None;
        validate_campaign(&catalog, &official, &ay).expect("unmaterialized final field");

        official.leaderboards[0].disposition = ScoreDisposition::PendingNormalization;
        official.leaderboards[0].evidence.clear();
        validate_campaign(&catalog, &official, &ay).expect("final field awaits normalization");

        official.leaderboards[0].disposition = ScoreDisposition::Pending;
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::OfficialDispositionMismatch {
                found: ScoreDisposition::Pending,
                ..
            }
        )));
    }

    #[test]
    fn unmaterialized_official_field_requires_evidence_and_no_competitors() {
        assert_eq!(
            serde_json::to_string(&ScoreDisposition::Unmaterialized)
                .expect("serialize disposition"),
            r#""unmaterialized""#
        );
        let (catalog, mut official, mut ay) = valid_bundle();
        official.leaderboards[0].disposition = ScoreDisposition::Unmaterialized;
        official.leaderboards[0].competitors.clear();
        official.leaderboards[0].denominator = None;
        ay.rows[0].disposition = ScoreDisposition::Pending;
        clear_ay_claims(&mut ay.rows[0]);
        validate_campaign(&catalog, &official, &ay).expect("evidence-bound source");

        official.leaderboards[0]
            .competitors
            .push(competitor(1, "Unexpected entrant", true));
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::CompetitorsForbidden { .. })));

        official.leaderboards[0].competitors.clear();
        official.leaderboards[0].evidence.clear();
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::MissingOfficialEvidence { .. }
        )));

        official.leaderboards[0].evidence = vec![CampaignIdentity {
            id: " evidence-with-padding ".to_owned(),
            sha256: Some("invalid".to_owned()),
        }];
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::InvalidIdentity { .. })));
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::InvalidSha256 { .. })));
    }

    #[test]
    fn unmaterialized_field_allows_only_claim_free_pending_or_unsupported_ay() {
        let (catalog, mut official, mut ay) = valid_bundle();
        official.leaderboards[0].disposition = ScoreDisposition::Unmaterialized;
        official.leaderboards[0].competitors.clear();
        official.leaderboards[0].denominator = None;

        ay.rows[0].disposition = ScoreDisposition::Pending;
        let issues = validation_issues(&catalog, &official, &ay);
        for field in ["score", "solves", "rank", "win"] {
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::AyClaimForbidden {
                    disposition: ScoreDisposition::Pending,
                    field: found_field,
                    ..
                } if *found_field == field
            )));
        }

        clear_ay_claims(&mut ay.rows[0]);
        validate_campaign(&catalog, &official, &ay).expect("pending AY");
        ay.rows[0].disposition = ScoreDisposition::Unsupported;
        validate_campaign(&catalog, &official, &ay).expect("unsupported AY");

        ay.rows[0].disposition = ScoreDisposition::Scored;
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::AyDispositionMismatch {
                official: ScoreDisposition::Unmaterialized,
                found: ScoreDisposition::Scored,
                ..
            }
        )));
    }

    #[test]
    fn pending_normalization_requires_no_field_or_evidence() {
        assert_eq!(
            serde_json::to_string(&ScoreDisposition::PendingNormalization)
                .expect("serialize disposition"),
            r#""pending-normalization""#
        );
        let (catalog, mut official, mut ay) = valid_bundle();
        official.leaderboards[0].disposition = ScoreDisposition::PendingNormalization;
        official.leaderboards[0].competitors.clear();
        official.leaderboards[0].denominator = None;
        official.leaderboards[0].evidence.clear();
        ay.rows[0].disposition = ScoreDisposition::Pending;
        clear_ay_claims(&mut ay.rows[0]);
        validate_campaign(&catalog, &official, &ay).expect("awaiting frozen artifact");

        official.leaderboards[0].evidence = vec![identity("not-yet-frozen")];
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::OfficialEvidenceForbidden {
                disposition: ScoreDisposition::PendingNormalization,
                ..
            }
        )));

        official.leaderboards[0].evidence.clear();
        official.leaderboards[0]
            .competitors
            .push(competitor(1, "Unexpected entrant", true));
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::CompetitorsForbidden { .. })));

        official.leaderboards[0].competitors.clear();
        ay.rows[0].disposition = ScoreDisposition::Unsupported;
        validate_campaign(&catalog, &official, &ay).expect("unsupported AY");
    }

    #[test]
    fn partial_official_field_allows_only_pending_or_unsupported_ay() {
        assert_eq!(
            serde_json::to_string(&ScoreDisposition::Partial).expect("serialize disposition"),
            r#""partial""#
        );
        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].status = "final-field-partial".to_owned();
        official.leaderboards[0].disposition = ScoreDisposition::Partial;
        ay.rows[0].disposition = ScoreDisposition::Pending;
        clear_ay_claims(&mut ay.rows[0]);
        validate_campaign(&catalog, &official, &ay).expect("pending AY with partial field");

        ay.rows[0].disposition = ScoreDisposition::Unsupported;
        validate_campaign(&catalog, &official, &ay).expect("unsupported AY with partial field");

        ay.rows[0].disposition = ScoreDisposition::Scored;
        ay.rows[0].score = Some(json!({"primary": 98}));
        ay.rows[0].solves = Some(SolveSummary {
            solved: 8,
            total: 10,
            solve_rate: 0.8,
        });
        ay.rows[0].rank = Some(2);
        ay.rows[0].win = Some(false);
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::AyDispositionMismatch {
                official: ScoreDisposition::Partial,
                found: ScoreDisposition::Scored,
                ..
            }
        )));
    }

    #[test]
    fn partial_official_field_requires_valid_competitors_and_evidence() {
        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].status = "final-field-partial".to_owned();
        official.leaderboards[0].disposition = ScoreDisposition::Partial;
        ay.rows[0].disposition = ScoreDisposition::Pending;
        clear_ay_claims(&mut ay.rows[0]);

        official.leaderboards[0].competitors[1].rank = 1;
        official.leaderboards[0].competitors[1].winner = true;
        official.leaderboards[0].evidence.clear();
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::RankTieNotExplicit { .. })));
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::MissingOfficialEvidence { .. }
        )));

        official.leaderboards[0].competitors.clear();
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::EmptyOfficialField { .. })));
    }

    #[test]
    fn partial_fields_allow_missing_scores_but_scored_fields_do_not() {
        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].status = "final-field-partial".to_owned();
        official.leaderboards[0].disposition = ScoreDisposition::Partial;
        official.leaderboards[0].competitors[0].score = Value::Null;
        ay.rows[0].disposition = ScoreDisposition::Pending;
        clear_ay_claims(&mut ay.rows[0]);
        validate_campaign(&catalog, &official, &ay).expect("medal-only partial field");

        catalog.tracks[0].status = "final".to_owned();
        official.leaderboards[0].disposition = ScoreDisposition::Scored;
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::MissingOfficialScore { .. })));
    }

    #[test]
    fn partial_ay_rows_cannot_carry_score_rank_or_win_claims() {
        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].status = "final-field-partial".to_owned();
        official.leaderboards[0].disposition = ScoreDisposition::Partial;
        ay.rows[0].disposition = ScoreDisposition::Partial;
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::AyDispositionMismatch {
                official: ScoreDisposition::Partial,
                found: ScoreDisposition::Partial,
                ..
            }
        )));
        for field in ["score", "solves", "rank", "win"] {
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::AyClaimForbidden {
                    disposition: ScoreDisposition::Partial,
                    field: found_field,
                    ..
                } if *found_field == field
            )));
        }
    }

    #[test]
    fn non_scored_official_rows_cannot_contain_competitors() {
        for (status, disposition) in [
            ("pending-results", ScoreDisposition::Pending),
            ("cancelled", ScoreDisposition::Cancelled),
            ("not-held", ScoreDisposition::NotHeld),
            ("experimental-no-ranking", ScoreDisposition::NotRanked),
        ] {
            let (mut catalog, mut official, mut ay) = valid_bundle();
            catalog.tracks[0].status = status.to_owned();
            official.leaderboards[0].disposition = disposition;
            ay.rows[0].disposition = disposition;
            clear_ay_claims(&mut ay.rows[0]);
            let issues = validation_issues(&catalog, &official, &ay);
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::CompetitorsForbidden {
                    disposition: found,
                    ..
                } if *found == disposition
            )));
        }
    }

    #[test]
    fn every_non_scored_ay_disposition_rejects_score_rank_and_win_claims() {
        for disposition in [
            ScoreDisposition::Partial,
            ScoreDisposition::Unmaterialized,
            ScoreDisposition::PendingNormalization,
            ScoreDisposition::Pending,
            ScoreDisposition::Cancelled,
            ScoreDisposition::NotHeld,
            ScoreDisposition::NotRanked,
            ScoreDisposition::Unsupported,
        ] {
            let (mut catalog, mut official, mut ay) = valid_bundle();
            match disposition {
                ScoreDisposition::Partial => {
                    catalog.tracks[0].status = "final-field-partial".to_owned();
                    official.leaderboards[0].disposition = disposition;
                }
                ScoreDisposition::Unmaterialized => {
                    official.leaderboards[0].disposition = disposition;
                    official.leaderboards[0].competitors.clear();
                }
                ScoreDisposition::PendingNormalization => {
                    official.leaderboards[0].disposition = disposition;
                    official.leaderboards[0].competitors.clear();
                    official.leaderboards[0].evidence.clear();
                }
                ScoreDisposition::Pending => {
                    catalog.tracks[0].status = "pending-results".to_owned();
                    official.leaderboards[0].disposition = disposition;
                    official.leaderboards[0].competitors.clear();
                }
                ScoreDisposition::Cancelled => {
                    catalog.tracks[0].status = "cancelled".to_owned();
                    official.leaderboards[0].disposition = disposition;
                    official.leaderboards[0].competitors.clear();
                }
                ScoreDisposition::NotHeld => {
                    catalog.tracks[0].status = "not-held".to_owned();
                    official.leaderboards[0].disposition = disposition;
                    official.leaderboards[0].competitors.clear();
                }
                ScoreDisposition::NotRanked => {
                    catalog.tracks[0].status = "experimental-no-ranking".to_owned();
                    official.leaderboards[0].disposition = disposition;
                    official.leaderboards[0].competitors.clear();
                }
                ScoreDisposition::Unsupported => {}
                ScoreDisposition::Scored => unreachable!(),
            }
            ay.rows[0].disposition = disposition;
            let issues = validation_issues(&catalog, &official, &ay);
            for field in ["score", "solves", "rank", "win"] {
                assert!(issues.iter().any(|issue| matches!(
                    issue,
                    CampaignValidationIssue::AyClaimForbidden {
                        disposition: found,
                        field: found_field,
                        ..
                    } if *found == disposition && *found_field == field
                )));
            }
        }
    }

    #[test]
    fn official_names_ranks_scores_and_evidence_fail_closed() {
        let (catalog, mut official, ay) = valid_bundle();
        official.leaderboards[0].competitors[0].name = " padded ".to_owned();
        official.leaderboards[0].competitors[0].rank = 0;
        official.leaderboards[0].competitors[0].score = Value::Null;
        official.leaderboards[0].evidence.clear();
        official.leaderboards[0].competitors[1].name = " padded ".to_owned();
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::InvalidCompetitorName { .. })));
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::DuplicateCompetitorName { .. }
        )));
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::InvalidCompetitorRank { .. })));
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::MissingOfficialScore { .. })));
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::MissingOfficialEvidence { .. }
        )));
    }

    #[test]
    fn official_ties_are_explicit_and_winners_match_eligibility() {
        let (catalog, mut official, mut ay) = valid_bundle();
        official.leaderboards[0].competitors[1].rank = 1;
        official.leaderboards[0].competitors[1].winner = true;
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::RankTieNotExplicit { .. })));

        for competitor in &mut official.leaderboards[0].competitors {
            competitor.tied = true;
        }
        official.leaderboards[0].competitors[1].score =
            official.leaderboards[0].competitors[0].score.clone();
        ay.rows[0].disposition = ScoreDisposition::Pending;
        clear_ay_claims(&mut ay.rows[0]);
        validate_campaign(&catalog, &official, &ay).expect("explicit winner tie");

        official.leaderboards[0].competitors[1].winner = false;
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::OfficialWinnerMismatch { .. }
        )));

        let (catalog, mut official, ay) = valid_bundle();
        official.leaderboards[0].competitors[0].tied = true;
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::SpuriousRankTie { .. })));
    }

    #[test]
    fn official_ranks_use_competition_sequence_and_eligible_rank_one() {
        let (catalog, mut official, ay) = valid_bundle();
        official.leaderboards[0].competitors[1].rank = 3;
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::InvalidCompetitionRankSequence {
                expected: 2,
                found: 3,
                ..
            }
        )));

        let (catalog, mut official, ay) = valid_bundle();
        official.leaderboards[0].competitors[0].eligible = false;
        official.leaderboards[0].competitors[0].winner = false;
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::NoEligibleCompetitor { .. })));
    }

    #[test]
    fn scored_ay_rows_require_a_ready_catalog_adapter() {
        let (mut catalog, official, ay) = valid_bundle();
        catalog.tracks[0].ay_adapter_status = "partial".to_owned();
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::AyAdapterNotReady {
                adapter_status,
                ..
            } if adapter_status == "partial"
        )));
    }

    #[test]
    fn scored_ay_rows_require_all_values_and_identities() {
        let required = [
            "score",
            "solves",
            "rank",
            "win",
            "candidate",
            "corpus",
            "scorer",
            "checker",
            "envelope",
            "evidence",
        ];
        for field in required {
            let (catalog, official, mut ay) = valid_bundle();
            let row = &mut ay.rows[0];
            match field {
                "score" => row.score = None,
                "solves" => row.solves = None,
                "rank" => row.rank = None,
                "win" => row.win = None,
                "candidate" => row.candidate = None,
                "corpus" => row.corpus = None,
                "scorer" => row.scorer = None,
                "checker" => row.checker = None,
                "envelope" => row.envelope = None,
                "evidence" => row.evidence.clear(),
                _ => unreachable!(),
            }
            let issues = validation_issues(&catalog, &official, &ay);
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::MissingAyScoredField {
                    field: found,
                    ..
                } if *found == field
            )));
        }
    }

    #[test]
    fn solve_rate_rank_and_win_are_checked_against_the_field() {
        let (catalog, official, mut ay) = valid_bundle();
        ay.rows[0].solves = Some(SolveSummary {
            solved: 11,
            total: 10,
            solve_rate: 1.0,
        });
        ay.rows[0].rank = Some(4);
        ay.rows[0].win = Some(true);
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::InvalidSolveSummary { .. })));
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::InvalidAyRank { .. })));
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::AyWinMismatch { .. })));

        ay.rows[0].solves = Some(SolveSummary {
            solved: 8,
            total: 10,
            solve_rate: 0.7,
        });
        ay.rows[0].rank = Some(1);
        ay.rows[0].win = Some(true);
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::InvalidSolveSummary { .. })));
    }

    #[test]
    fn registered_scorer_recomputes_official_and_ay_ranks() {
        let (catalog, mut official, ay) = valid_bundle();
        official.leaderboards[0].competitors[1].score = json!({"solved": 10, "cpu_seconds": 1});
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::OfficialScoreRankMismatch {
                name,
                reported: 2,
                expected: 1,
                ..
            } if name == "Reference Runner-up"
        )));

        let (catalog, official, mut ay) = valid_bundle();
        ay.rows[0].score = Some(json!({"solved": 10, "cpu_seconds": 1}));
        ay.rows[0].solves = Some(SolveSummary {
            solved: 10,
            total: 10,
            solve_rate: 1.0,
        });
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::AyScoreRankMismatch {
                reported: 2,
                expected: 1,
                ..
            }
        )));
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::AyWinMismatch { .. })));
    }

    #[test]
    fn correct_count_scorer_recomputes_ties_and_ay_rank() {
        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].official_score_kind = "correct-count".to_owned();
        catalog.tracks[0].official_score_direction = "maximize".to_owned();
        official.leaderboards[0].competitors[0].score = json!({"correct": 9});
        official.leaderboards[0].competitors[1].score = json!({"correct": 8});
        ay.rows[0].score = Some(json!({"correct": 8}));

        validate_campaign(&catalog, &official, &ay)
            .expect("correct-count field and AY insertion rank should validate");

        official.leaderboards[0].competitors[1].score = json!({"correct": 9});
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::OfficialScoreRankMismatch {
                name,
                reported: 2,
                expected: 1,
                ..
            } if name == "Reference Runner-up"
        )));
    }

    #[test]
    fn average_par2_scorer_compares_exact_rationals_and_rejects_zero_denominator() {
        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].official_score_kind = "average-par2".to_owned();
        catalog.tracks[0].official_score_direction = "minimize".to_owned();
        official.leaderboards[0].competitors[0].score =
            json!({"average_par2_numerator": 4, "average_par2_denominator": 1});
        official.leaderboards[0].competitors[1].score =
            json!({"average_par2_numerator": 9, "average_par2_denominator": 2});
        ay.rows[0].score =
            Some(json!({"average_par2_numerator": 17, "average_par2_denominator": 4}));

        validate_campaign(&catalog, &official, &ay)
            .expect("exact average PAR-2 field and AY insertion rank should validate");

        official.leaderboards[0].competitors[1].score =
            json!({"average_par2_numerator": 1, "average_par2_denominator": 0});
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::InvalidOfficialScore { reason, .. }
                if reason.contains("denominator must be nonzero")
        )));
    }

    #[test]
    fn official_ratio_scorer_maximizes_exact_values_and_rejects_zero_denominator() {
        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].official_score_kind = "official-complexity-category-score".to_owned();
        catalog.tracks[0].official_score_direction = "maximize".to_owned();
        official.leaderboards[0].competitors[0].score =
            json!({"official_score_numerator": 3, "official_score_denominator": 2});
        official.leaderboards[0].competitors[1].score =
            json!({"official_score_numerator": 4, "official_score_denominator": 3});
        ay.rows[0].score =
            Some(json!({"official_score_numerator": 7, "official_score_denominator": 5}));

        validate_campaign(&catalog, &official, &ay)
            .expect("exact rational field and AY insertion rank should validate");

        official.leaderboards[0].competitors[1].score =
            json!({"official_score_numerator": 1, "official_score_denominator": 0});
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::InvalidOfficialScore { reason, .. }
                if reason.contains("denominator must be nonzero")
        )));
    }

    #[test]
    fn certified_solved_count_scorer_recomputes_ties_and_ay_rank() {
        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].official_score_kind = "certified-solved-count".to_owned();
        catalog.tracks[0].official_score_direction = "maximize".to_owned();
        official.leaderboards[0].competitors[0].score = json!({"certified_solved": 9});
        official.leaderboards[0].competitors[1].score = json!({"certified_solved": 8});
        ay.rows[0].score = Some(json!({"certified_solved": 8}));

        validate_campaign(&catalog, &official, &ay)
            .expect("certified-solved field and AY insertion rank should validate");

        official.leaderboards[0].competitors[1].score = json!({"certified_solved": 9});
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::OfficialScoreRankMismatch {
                name,
                reported: 2,
                expected: 1,
                ..
            } if name == "Reference Runner-up"
        )));
    }

    #[test]
    fn correct_yes_no_count_scorer_recomputes_ties_and_ay_rank() {
        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].official_score_kind =
            "correct-yes-no-count-with-disqualification".to_owned();
        catalog.tracks[0].official_score_direction = "maximize".to_owned();
        official.leaderboards[0].competitors[0].score = json!({"correct_yes": 5, "correct_no": 4});
        official.leaderboards[0].competitors[1].score = json!({"correct_yes": 5, "correct_no": 3});
        ay.rows[0].score = Some(json!({"correct_yes": 4, "correct_no": 4}));

        validate_campaign(&catalog, &official, &ay)
            .expect("correct YES/NO field and AY insertion rank should validate");

        official.leaderboards[0].competitors[1].score = json!({"correct_yes": 5, "correct_no": 4});
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::OfficialScoreRankMismatch {
                name,
                reported: 2,
                expected: 1,
                ..
            } if name == "Reference Runner-up"
        )));
    }

    #[test]
    fn acceptable_solution_scorer_uses_average_time_and_missing_time_loses() {
        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].official_score_kind = "acceptable-solutions-then-average-time".to_owned();
        catalog.tracks[0].official_score_direction = "mixed-lexicographic".to_owned();
        official.leaderboards[0].competitors[0].score =
            json!({"acceptable_solutions": 9, "average_time_centiseconds": 100});
        official.leaderboards[0].competitors[1].score =
            json!({"acceptable_solutions": 8, "average_time_centiseconds": null});
        ay.rows[0].score =
            Some(json!({"acceptable_solutions": 8, "average_time_centiseconds": 10}));

        validate_campaign(&catalog, &official, &ay)
            .expect("finite average time should outrank a missing average at equal count");

        official.leaderboards[0].competitors[1].score =
            json!({"acceptable_solutions": 8, "average_time_centiseconds": 5});
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::AyScoreRankMismatch {
                reported: 2,
                expected: 3,
                ..
            }
        )));
    }

    #[test]
    fn solved_count_average_time_scorer_uses_solved_field() {
        let (mut catalog, mut official, mut ay) = valid_bundle();
        catalog.tracks[0].official_score_kind = "solved-count-then-average-time".to_owned();
        catalog.tracks[0].official_score_direction = "mixed-lexicographic".to_owned();
        official.leaderboards[0].competitors[0].score =
            json!({"solved": 9, "average_time_centiseconds": 100});
        official.leaderboards[0].competitors[1].score =
            json!({"solved": 8, "average_time_centiseconds": null});
        ay.rows[0].score = Some(json!({"solved": 8, "average_time_centiseconds": 10}));

        validate_campaign(&catalog, &official, &ay)
            .expect("EPR-style solved count should be the primary score");
    }

    #[test]
    fn scored_fields_require_denominator_and_registered_comparator() {
        let (catalog, mut official, ay) = valid_bundle();
        official.leaderboards[0].denominator = None;
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::MissingOfficialDenominator { .. }
        )));

        let (mut catalog, official, ay) = valid_bundle();
        catalog.tracks[0].official_score_kind = "opaque-score".to_owned();
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::UnsupportedScoreComparator {
                score_kind,
                ..
            } if score_kind == "opaque-score"
        )));
    }

    #[test]
    fn ay_solve_summary_is_bound_to_official_denominator_and_typed_score() {
        let (catalog, official, mut ay) = valid_bundle();
        ay.rows[0].solves = Some(SolveSummary {
            solved: 7,
            total: 9,
            solve_rate: 7.0 / 9.0,
        });
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::AyDenominatorMismatch {
                reported: 9,
                expected: 10,
                ..
            }
        )));
        assert!(issues.iter().any(|issue| matches!(
            issue,
            CampaignValidationIssue::AySolvedCountMismatch {
                score_solved: 8,
                summary_solved: 7,
                ..
            }
        )));

        ay.rows[0].solves = Some(SolveSummary {
            solved: 0,
            total: 0,
            solve_rate: 0.0,
        });
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::InvalidSolveSummary { .. })));
    }

    #[test]
    fn malformed_identity_and_digest_fail_closed() {
        let (catalog, official, mut ay) = valid_bundle();
        ay.rows[0].candidate = Some(CampaignIdentity {
            id: " candidate ".to_owned(),
            sha256: Some("ABC".to_owned()),
        });
        let issues = validation_issues(&catalog, &official, &ay);
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::InvalidIdentity { .. })));
        assert!(issues
            .iter()
            .any(|issue| matches!(issue, CampaignValidationIssue::InvalidSha256 { .. })));
    }

    #[test]
    fn official_and_scored_ay_provenance_require_sha256() {
        let (catalog, mut official, mut ay) = valid_bundle();
        official.leaderboards[0].evidence[0].sha256 = None;
        ay.rows[0].candidate.as_mut().expect("candidate").sha256 = None;
        ay.rows[0].evidence[0].sha256 = None;
        let issues = validation_issues(&catalog, &official, &ay);
        for field in ["official evidence", "candidate", "evidence"] {
            assert!(issues.iter().any(|issue| matches!(
                issue,
                CampaignValidationIssue::MissingSha256 {
                    field: found,
                    ..
                } if *found == field
            )));
        }
    }

    #[test]
    fn normalized_json_rejects_unknown_fields() {
        let official = r#"{
            "schema_version": 1,
            "leaderboards": [],
            "unexpected": true
        }"#;
        assert!(serde_json::from_str::<OfficialFieldReport>(official).is_err());

        let ay = r#"{
            "schema_version": 1,
            "rows": [],
            "unexpected": true
        }"#;
        assert!(serde_json::from_str::<AyScoreReport>(ay).is_err());
    }

    fn clear_ay_claims(row: &mut AyScoreRow) {
        row.score = None;
        row.solves = None;
        row.rank = None;
        row.win = None;
    }
}
