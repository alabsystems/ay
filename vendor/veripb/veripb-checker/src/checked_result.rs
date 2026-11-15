// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Typed statements emitted only after the complete derivation succeeds.

use std::fmt::{self, Display};

use malachite_bigint::BigInt;
use veripb_rules::{Bound, ConclusionResult, OutputGuarantee, OutputType};

use crate::rules::conclusion::{conclusion_status_line, verdict_prefix};

/// The logical statement checked by a conclusion or output rule.
#[derive(Debug, Clone)]
pub enum CheckedClaim {
    Conclusion {
        result: ConclusionResult,
        lower_bound_or_count: Option<Bound>,
        upper_bound: Option<Bound>,
    },
    Output {
        guarantee: OutputGuarantee,
        output_type: OutputType,
        objective_ceiling: Option<BigInt>,
    },
}

/// Whether a checked statement depends on an unproved assumption or weakened check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatementAssurance {
    Verified,
    UnderAssertions,
    UnderWeakenedGuarantees,
    UnderAssertionsAndWeakenedGuarantees,
}

/// A checked statement with its exact assurance and optional objective bounds.
///
/// Construction is internal to the checker. Callers inspect typed claims instead
/// of treating a matching substring on stdout as a certificate.
#[derive(Debug, Clone)]
pub struct CheckedStatement {
    claim: CheckedClaim,
    assertion_used: bool,
    weakened_guarantees: bool,
    emit: bool,
}

impl CheckedStatement {
    pub(crate) fn conclusion(
        result: ConclusionResult,
        lower_bound_or_count: Option<Bound>,
        upper_bound: Option<Bound>,
        assertion_used: bool,
        weakened_guarantees: bool,
        emit: bool,
    ) -> Self {
        Self {
            claim: CheckedClaim::Conclusion {
                result,
                lower_bound_or_count,
                upper_bound,
            },
            assertion_used,
            weakened_guarantees,
            emit,
        }
    }

    pub(crate) fn output(
        guarantee: OutputGuarantee,
        output_type: OutputType,
        objective_ceiling: Option<BigInt>,
        assertion_used: bool,
        emit: bool,
    ) -> Self {
        Self {
            claim: CheckedClaim::Output {
                guarantee,
                output_type,
                objective_ceiling,
            },
            assertion_used,
            weakened_guarantees: false,
            emit,
        }
    }

    pub fn claim(&self) -> &CheckedClaim {
        &self.claim
    }

    pub fn assurance(&self) -> StatementAssurance {
        match (self.assertion_used, self.weakened_guarantees) {
            (false, false) => StatementAssurance::Verified,
            (true, false) => StatementAssurance::UnderAssertions,
            (false, true) => StatementAssurance::UnderWeakenedGuarantees,
            (true, true) => StatementAssurance::UnderAssertionsAndWeakenedGuarantees,
        }
    }

    pub fn is_substantive(&self) -> bool {
        !matches!(
            self.claim,
            CheckedClaim::Conclusion {
                result: ConclusionResult::None,
                ..
            } | CheckedClaim::Output {
                guarantee: OutputGuarantee::None,
                ..
            }
        )
    }

    pub fn should_emit(&self) -> bool {
        self.emit
    }

    pub fn checks_output_file(&self) -> bool {
        matches!(
            self.claim,
            CheckedClaim::Output {
                output_type: OutputType::File,
                ..
            }
        )
    }
}

impl Display for CheckedStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.claim {
            CheckedClaim::Conclusion {
                result,
                lower_bound_or_count,
                upper_bound,
            } => f.write_str(&conclusion_status_line(
                result,
                lower_bound_or_count.as_ref(),
                upper_bound.as_ref(),
                self.assertion_used,
                self.weakened_guarantees,
            )),
            CheckedClaim::Output {
                guarantee,
                objective_ceiling,
                ..
            } => {
                let kind = match guarantee {
                    OutputGuarantee::Derivable => "DERIVABLE",
                    OutputGuarantee::Equisatisfiable => "EQUISATISFIABLE",
                    OutputGuarantee::Equioptimal => "EQUIOPTIMAL",
                    OutputGuarantee::Equienumerable => "EQUIENUMERABLE",
                    OutputGuarantee::None => "NONE",
                };
                write!(
                    f,
                    "{} OUTPUT {kind}",
                    verdict_prefix(self.assertion_used, false)
                )?;
                if matches!(guarantee, OutputGuarantee::Equioptimal) {
                    if let Some(ceiling) = objective_ceiling {
                        write!(f, " FOR obj < {ceiling}")?;
                    }
                }
                Ok(())
            }
        }
    }
}
