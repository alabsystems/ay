// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict proofs as ONE predicate that every route reads.
//!
//! Strict proofs are requested in two spellings: `--strict-proofs` (`--rigor
//! strict`) on the command line, and `(set-option :check-proofs-strict true)`
//! in the script. They make one promise, so the strict admission gates — the
//! SMT-LIB one (`run::strict_admission_requested`) and the CHC ones
//! (`chc_runner::proof_gates::ChcProofGates`) — read
//! [`StrictProofsRequest::requested`], never the flag alone. A gate that read
//! only [`STRICT_PROOFS_ENABLED`] kept its promise for one spelling and
//! broke it for the other: the CHC runner skipped the UNSAFE counterexample
//! ground check, the SAFE invariant re-discharge and the missing-certificate
//! refusal for a HORN script that set the option and passed no flag, and
//! published the unchecked verdict.
//!
//! Where the in-script option is read depends on the route: an SMT-LIB route
//! asks its executor ([`ay_dpll::Executor::script_strict_proofs_requested`]);
//! the CHC routes, which never hand the script to an executor, read the script
//! text with [`ay_frontend::script_requests_strict_proofs`]. Both are the same
//! read of the same option table (`Context::check_proofs_strict_requested`).

use std::sync::atomic::Ordering;

use super::STRICT_PROOFS_ENABLED;

/// Which spellings requested strict proofs for one decision.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct StrictProofsRequest {
    /// `--strict-proofs` / `--rigor strict`.
    flag: bool,
    /// `(set-option :check-proofs-strict true)` in the script.
    script_option: bool,
}

impl StrictProofsRequest {
    /// The request for a decision whose script has (or has not) set the
    /// in-script option, combined with the command-line flag.
    pub(crate) fn with_script_option(script_option: bool) -> Self {
        Self {
            flag: STRICT_PROOFS_ENABLED.load(Ordering::SeqCst),
            script_option,
        }
    }

    /// A request with explicit spellings (tests and callers that already hold
    /// the flag value).
    #[cfg(test)]
    pub(crate) const fn new(flag: bool, script_option: bool) -> Self {
        Self {
            flag,
            script_option,
        }
    }

    /// THE strict predicate: either spelling.
    pub(crate) const fn requested(self) -> bool {
        self.flag || self.script_option
    }

    /// The spelling a refusal names, preferring the flag when both are set.
    pub(crate) const fn spelling(self) -> Option<&'static str> {
        if self.flag {
            Some("--strict-proofs")
        } else if self.script_option {
            Some("(set-option :check-proofs-strict true)")
        } else {
            None
        }
    }
}

/// [`StrictProofsRequest::requested`] for a decision whose script has (or has
/// not) set the in-script option.
pub(crate) fn strict_proofs_requested(script_option: bool) -> bool {
    StrictProofsRequest::with_script_option(script_option).requested()
}
