// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The proof gates of one CHC decision.

use std::sync::atomic::Ordering;

use crate::strict_request::StrictProofsRequest;
use crate::SELF_CHECK_ENABLED;

/// The proof gates one CHC decision runs under, fixed when its script is read.
///
/// Strictness is [`StrictProofsRequest`]: `--strict-proofs` OR the script's
/// `(set-option :check-proofs-strict true)`. Every CHC strict gate — the
/// missing-certificate refusal, the required-certificate disposition, the SAFE
/// invariant re-discharge (STEP C) and the UNSAFE counterexample ground check
/// (STEP D) — reads [`Self::strict`], so the two spellings cannot diverge. They
/// did: every one of these gates read only the flag, and a HORN script that set
/// the option published `sat`/`unsat` with none of them run, on the file route
/// and on `--stdin`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ChcProofGates {
    pub(super) strict: StrictProofsRequest,
    pub(super) self_check: bool,
}

impl ChcProofGates {
    /// The gates for `content`. `inherited_script_option` is the in-script
    /// option set on the route's executor before the CHC text began (the
    /// incremental route hands the CHC runner only the commands after
    /// `(set-logic HORN)`).
    pub(super) fn for_script(content: &str, inherited_script_option: bool) -> Self {
        Self {
            strict: StrictProofsRequest::with_script_option(
                inherited_script_option || ay_frontend::script_requests_strict_proofs(content),
            ),
            self_check: SELF_CHECK_ENABLED.load(Ordering::SeqCst),
        }
    }

    /// Whether strict proofs were requested, in either spelling.
    pub(super) fn strict(self) -> bool {
        self.strict.requested()
    }

    /// Whether a definitive verdict must pass the independent re-checks (the
    /// SAFE re-discharge and the UNSAFE ground check) before it prints: under
    /// a strict request, and under `--self-check` (`--rigor certified`), which
    /// ranks above strict and so must never publish a verdict strict demotes.
    pub(super) fn independent_recheck(self) -> bool {
        self.strict() || self.self_check
    }

    /// The spelling that demanded the independent re-checks, for a demotion.
    pub(super) fn independent_recheck_spelling(self) -> String {
        self.required_certificate_gate_name()
            .unwrap_or_else(|| "--strict-proofs".to_string())
    }

    /// The gate that makes a CHC certificate mandatory, as a refusal names it.
    pub(super) fn required_certificate_gate_name(self) -> Option<String> {
        match (self.strict.spelling(), self.self_check) {
            (Some(strict), true) => Some(format!("{strict}/--self-check")),
            (Some(strict), false) => Some(strict.to_string()),
            (None, true) => Some("--self-check".to_string()),
            (None, false) => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{
        chc_certificate_failure_disposition, ChcCertificateFailureDisposition as Disposition,
    };
    use super::{ChcProofGates, StrictProofsRequest};

    fn gates(flag: bool, script_option: bool, self_check: bool) -> ChcProofGates {
        ChcProofGates {
            strict: StrictProofsRequest::new(flag, script_option),
            self_check,
        }
    }

    /// The in-script option is a strict request in its own right: it makes the
    /// certificate mandatory and every strict gate fire, and the refusal names
    /// the spelling the caller used.
    #[test]
    fn the_in_script_option_is_a_required_certificate_gate() {
        let option = "(set-option :check-proofs-strict true)";
        let flag_name = Some("--strict-proofs".to_string());
        let option_name = Some(option.to_string());
        let option_self_check = Some(format!("{option}/--self-check"));
        let self_check_name = Some("--self-check".to_string());
        for (flag, script_option, self_check, strict, name) in [
            (false, false, false, false, None),
            (true, false, false, true, flag_name.clone()),
            (false, true, false, true, option_name),
            (true, true, false, true, flag_name),
            (false, true, true, true, option_self_check),
            (false, false, true, false, self_check_name),
        ] {
            let gates = gates(flag, script_option, self_check);
            assert_eq!(gates.strict(), strict, "{gates:?}");
            // Certified ranks above strict: it runs strict's re-checks too.
            assert_eq!(gates.independent_recheck(), name.is_some(), "{gates:?}");
            if let Some(name) = &name {
                assert_eq!(&gates.independent_recheck_spelling(), name, "{gates:?}");
            }
            assert_eq!(gates.required_certificate_gate_name(), name, "{gates:?}");
            let expected = if name.is_some() {
                Disposition::Required
            } else {
                Disposition::Optional
            };
            assert_eq!(
                chc_certificate_failure_disposition(
                    true,
                    gates.required_certificate_gate_name().as_deref()
                ),
                expected,
                "{gates:?}"
            );
        }
    }
}
