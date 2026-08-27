// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use super::{check_claims::ClaimReportSeal, checking_main::CheckReportSeal};

/// The checker's verdict. The word VERIFIED is RESERVED.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckStatus {
    /// Every claim is SUCCINCT and every block re-verified. Exit 0.
    Verified,
    /// SOME claim re-verified exactly and nothing was refuted, but at least
    /// one claim is REPLAY or NONE. Exit 11.
    ///
    /// This is a REFINEMENT OF [`Self::Unverified`], never of
    /// [`Self::Verified`]: it is a non-zero exit, it means the certificate as
    /// a whole is not proven, and no flag turns it into exit 0.
    ///
    /// # Why it exists
    ///
    /// A generic MILP optimum can carry an exactly checked primal point while
    /// having no exported proof that nothing beats it. A consumer must be able
    /// to distinguish that useful checked half from a file where nothing
    /// checked out, without upgrading the unproved optimum to `Verified`.
    ///
    /// Splitting the code, rather than upgrading the aggregate, is what keeps
    /// this honest: "some evidence checked out" and "this verdict is proven"
    /// are different statements and now have different exit codes.
    Partial,
    /// NOTHING re-verified: every claim is REPLAY or NONE. Exit 10.
    Unverified,
    /// A SUCCINCT block failed to verify. Exit 20.
    Refuted,
    /// A digest, shape, or the model itself did not match. Exit 30.
    Mismatch,
}

impl CheckStatus {
    /// The process exit code this status reserves.
    #[must_use]
    pub fn exit_code(self) -> i32 {
        match self {
            Self::Verified => 0,
            Self::Partial => 11,
            Self::Unverified => 10,
            Self::Refuted => 20,
            Self::Mismatch => 30,
        }
    }

    /// The status word.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            Self::Verified => "VERIFIED",
            Self::Partial => "PARTIAL",
            Self::Unverified => "UNVERIFIED",
            Self::Refuted => "REFUTED",
            Self::Mismatch => "MISMATCH",
        }
    }
}

/// One claim's independent re-check.
///
/// Claim reports are checker-created evidence. Their fields and constructor
/// are private to the checker, while consumers receive read-only accessors.
///
/// ```compile_fail
/// use ay_milp::cert_io::{ClaimReport, EvidenceKind};
///
/// let _forged = ClaimReport {
///     name: "primal".to_owned(),
///     kind: EvidenceKind::Succinct,
///     verified: true,
///     detail: "unchecked".to_owned(),
/// };
/// ```
///
/// ```compile_fail
/// use ay_milp::cert_io::ClaimReport;
///
/// fn forge(mut report: ClaimReport) {
///     report.verified = true;
/// }
/// ```
#[derive(Debug, Clone)]
pub struct ClaimReport {
    /// The claim's name.
    name: String,
    /// The kind the certificate asserted.
    kind: EvidenceKind,
    /// Whether this checker re-derived it. NEVER true for a REPLAY or NONE
    /// claim, whatever the certificate says.
    verified: bool,
    /// Human-readable detail.
    detail: String,
}

impl ClaimReport {
    pub(super) fn new(
        _seal: ClaimReportSeal,
        name: String,
        kind: EvidenceKind,
        verified: bool,
        detail: String,
    ) -> Self {
        Self {
            name,
            kind,
            verified: verified && kind == EvidenceKind::Succinct,
            detail,
        }
    }

    /// The claim's name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The evidence kind asserted by the certificate.
    #[must_use]
    pub const fn kind(&self) -> EvidenceKind {
        self.kind
    }

    /// Whether the checker independently re-derived this claim.
    #[must_use]
    pub const fn is_verified(&self) -> bool {
        self.verified
    }

    /// Human-readable detail from the check.
    #[must_use]
    pub fn detail(&self) -> &str {
        &self.detail
    }

    /// This claim's standing, as one of the THREE outcomes a consumer must be
    /// able to tell apart.
    ///
    /// The pair `(kind, verified)` already encodes it, but only if the reader
    /// knows that `SUCCINCT` + `!verified` means the exported block was
    /// CHECKED AND FOUND WRONG, while `NONE`/`REPLAY` + `!verified` means
    /// there was nothing to check. Conflating those two is exactly the
    /// mistake this method exists to prevent.
    #[must_use]
    pub fn standing(&self) -> ClaimStanding {
        match (self.verified, self.kind) {
            (true, _) => ClaimStanding::Verified,
            (false, EvidenceKind::Succinct) => ClaimStanding::Refuted,
            (false, _) => ClaimStanding::Unbacked,
        }
    }
}

/// What a single claim's re-check established.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClaimStanding {
    /// An exported object was re-derived exactly against the model.
    Verified,
    /// An exported SUCCINCT object was checked and DID NOT hold.
    Refuted,
    /// Nothing to check: the claim carries `NONE` or `REPLAY` evidence.
    Unbacked,
}

/// The checker's full report.
///
/// Reports are constructed only by the checker. A consumer can inspect the
/// checker-derived status and details, but cannot fabricate or mutate them.
///
/// ```compile_fail
/// use ay_milp::cert_io::{CheckReport, CheckStatus};
///
/// let _forged = CheckReport {
///     status: CheckStatus::Verified,
///     claims: Vec::new(),
///     notes: Vec::new(),
/// };
/// ```
///
/// ```compile_fail
/// use ay_milp::cert_io::{check, CheckStatus};
///
/// let mut report = check("", "");
/// report.status = CheckStatus::Verified;
/// ```
#[derive(Debug, Clone)]
pub struct CheckReport {
    /// The overall status.
    status: CheckStatus,
    /// Per-claim breakdown.
    claims: Vec<ClaimReport>,
    /// Notes about the model binding and anything the checker refused.
    notes: Vec<String>,
}

impl CheckReport {
    pub(super) fn new(
        _seal: CheckReportSeal,
        status: CheckStatus,
        claims: Vec<ClaimReport>,
        notes: Vec<String>,
    ) -> Self {
        let status = if status == CheckStatus::Verified
            && (claims.is_empty() || claims.iter().any(|claim| !claim.is_verified()))
        {
            CheckStatus::Unverified
        } else {
            status
        };
        Self {
            status,
            claims,
            notes,
        }
    }

    /// The checker-derived aggregate status.
    #[must_use]
    pub const fn status(&self) -> CheckStatus {
        self.status
    }

    /// Per-claim reports, in certificate order, including duplicate names.
    ///
    /// No first-match name lookup is exposed because duplicate names remain
    /// distinct checker results.
    #[must_use]
    pub fn claims(&self) -> &[ClaimReport] {
        &self.claims
    }

    /// Notes about model binding and refused evidence.
    #[must_use]
    pub fn notes(&self) -> &[String] {
        &self.notes
    }

    /// Claim names in a given standing, in certificate order.
    #[must_use]
    pub fn claims_in(&self, standing: ClaimStanding) -> Vec<&str> {
        self.claims
            .iter()
            .filter(|c| c.standing() == standing)
            .map(|c| c.name.as_str())
            .collect()
    }

    /// THE CENSUS LINE: one grep-able line naming every claim by standing.
    ///
    /// The aggregate status word answers "is this verdict proven?". It cannot
    /// answer "which of the things this certificate asserts did you actually
    /// re-derive?", and that is the question a consumer holding a `PARTIAL`
    /// needs answered — a verified `primal` on a SAT verdict is a point it may
    /// rely on, whether or not the dual half exists in this build.
    ///
    /// Empty lists print `-` rather than nothing so the three fields are
    /// always present and a parser never has to distinguish "absent" from
    /// "empty".
    #[must_use]
    pub fn census(&self) -> String {
        let join = |s: ClaimStanding| {
            let v = self.claims_in(s);
            if v.is_empty() {
                "-".to_owned()
            } else {
                v.join(",")
            }
        };
        format!(
            "CLAIMS verified={} refuted={} unbacked={}",
            join(ClaimStanding::Verified),
            join(ClaimStanding::Refuted),
            join(ClaimStanding::Unbacked),
        )
    }
}
