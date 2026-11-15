// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! How much evidence backs a published `unsat`, and — when it has no checked
//! derivation — what AY re-ran to corroborate it.
//!
//! #evidence-stage-3. A large share of AY's refutations are admitted by
//! `discharge_trust_steps_for_certification`, and neither of its accepting arms
//! appeared in the emitted artifact. One re-checks every deferred clause as a
//! standalone theory tautology; the other re-decides the authored obligation in
//! a fresh `Executor`. The only trace either left was a statistics counter.
//!
//! P4 of the 2026-10-02 evidence policy (`~/ay-bench/dtrust/POLICY.md`) makes
//! the labels honest. The re-solve arm is REPRODUCIBILITY evidence, never
//! checkability evidence: it clones the same context into the same engine
//! running the same preprocessing, so it is structurally incapable of catching
//! a systematic bug in a lane both copies share. Measured: on the D7 list 197 of
//! 202 such re-solves rebuild a byte-identical certificate with 11 lane switches
//! off, and on the Sep-16/20 mains it confirmed all 18 historical wrong
//! `discharged-trust` unsats. So it is labelled [`UnsatEvidenceLevel::E1`] and
//! no longer counted as "independently verified"; `--rigor strict` is the
//! posture that carries the full evidence promise.

use crate::executor::StrengtheningSet;

/// The evidence level of a published `unsat` (the campaign's EV1 scale, as far
/// as it can be read off the certificate AY consumed).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum UnsatEvidenceLevel {
    /// No checked refutation at all: the competition posture's raw admission.
    E0,
    /// AY's own code re-derived what the refutation could not show: a
    /// `discharged-trust` admission (a deferred hole discharged by a re-solve
    /// or a standalone-tautology re-check), a `checked-sat-refutation` with a
    /// `Generic` theory premise re-derived by AY's semantic-conflict verifier,
    /// or an exact theorem that seals such a refutation.
    E1,
    /// A checker verified the refutation: AY's strict proof checker end to end,
    /// or an independent RUP/resolution replay whose every premise is strictly
    /// authenticated against the authored query.
    E2,
}

impl UnsatEvidenceLevel {
    /// The certificate-line spelling.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::E0 => "E0",
            Self::E1 => "E1",
            Self::E2 => "E2",
        }
    }
}

/// Which arm of the deferred-trust discharge admitted a refutation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CorroborationMethod {
    /// Arm (3): every clause the collecting checker deferred was re-decided on
    /// its own by AY's specialised checkers or a strictly checked nested solve
    /// — as a theory tautology (`not C` unsat) or as entailed by the authored
    /// problem (`P and not C` unsat; `api::proofs::discharge_trust_clause`).
    /// The original proof's structure was not trusted for any of them. A
    /// symmetry-breaking fact is neither valid nor entailed, so it can pass
    /// only through a nested solve that applies the same strengthening, which
    /// P1 forbids.
    StandaloneTautology,
    /// Arm (4), or a nested re-solve accepted on the same screen: a fresh
    /// `Executor` re-decided the obligation as `unsat` under fixed
    /// conflict/decision bounds. Same code, same preprocessing.
    Resolve,
    /// Arm (4a): a fresh `Executor` running the same engine, under arm (4)'s
    /// bounds and proof screen, re-decided that the authored obligation
    /// ENTAILS every deferred clause (`P ∧ (¬C1 ∨ … ∨ ¬Cn)` is `unsat`);
    /// every other step of the proof was strictly validated. Same evidence
    /// class as arm (4), a narrower question: it reproduces the deferred
    /// clauses, it does not check them.
    Entailment,
}

impl CorroborationMethod {
    /// Stable census tag. `resolve` replaces the retired
    /// `fresh-executor-resolve` and `entailment` the retired
    /// `fresh-executor-entailment`; a census reading older output maps each
    /// to the new tag with `disabled=none`.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::StandaloneTautology => "standalone-tautology",
            Self::Resolve => "resolve",
            Self::Entailment => "entailment",
        }
    }
}

/// Where the corroboration ran: on the published query itself, or inside a
/// nested probe whose refutation an exact theorem sealed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CorroborationSource {
    /// The published query's own deferred-trust discharge.
    Direct,
    /// The probe that refuted a proper subset of the authored roots.
    NestedAuthoredSubset,
    /// One branch probe of the RoundingMode finite-domain expansion.
    NestedRmDomainExpansion,
    /// A nested re-solve of a closed sentence (or its negation).
    NestedClosedSentence,
}

impl CorroborationSource {
    /// Stable census tag.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Direct => "direct",
            Self::NestedAuthoredSubset => "nested:authored-subset",
            Self::NestedRmDomainExpansion => "nested:rm-domain-expansion",
            Self::NestedClosedSentence => "nested:closed-sentence",
        }
    }
}

/// What corroborated a refutation that has no checked derivation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnsatCorroboration {
    method: CorroborationMethod,
    source: CorroborationSource,
    disabled: StrengtheningSet,
}

impl UnsatCorroboration {
    /// Arm (3) on the published query.
    #[must_use]
    pub const fn standalone_tautology() -> Self {
        Self {
            method: CorroborationMethod::StandaloneTautology,
            source: CorroborationSource::Direct,
            disabled: StrengtheningSet::EMPTY,
        }
    }

    /// A re-solve that ran without `disabled`: the strengthenings the solve it
    /// corroborates applied. Every checking re-solve runs with all of them off
    /// (P1), so `disabled` empty means the re-solve walked the same code.
    #[must_use]
    pub const fn resolve(disabled: StrengtheningSet) -> Self {
        Self {
            method: CorroborationMethod::Resolve,
            source: CorroborationSource::Direct,
            disabled,
        }
    }

    /// Arm (4a): a re-solve that ran without `disabled` (as for
    /// [`Self::resolve`]) re-decided that the authored obligation entails
    /// every deferred clause.
    #[must_use]
    pub const fn entailment(disabled: StrengtheningSet) -> Self {
        Self {
            method: CorroborationMethod::Entailment,
            source: CorroborationSource::Direct,
            disabled,
        }
    }

    /// The same corroboration, seen from the theorem that sealed the probe it
    /// ran in.
    #[must_use]
    pub const fn nested(self, source: CorroborationSource) -> Self {
        Self { source, ..self }
    }

    /// Which arm admitted the refutation.
    #[must_use]
    pub const fn method(self) -> CorroborationMethod {
        self.method
    }

    /// Where it ran.
    #[must_use]
    pub const fn source(self) -> CorroborationSource {
        self.source
    }

    /// The strengthenings the corroborating re-solve ran without.
    #[must_use]
    pub const fn disabled(self) -> StrengtheningSet {
        self.disabled
    }

    /// Stable census tag of the method (kept for callers of the old enum).
    #[must_use]
    pub const fn tag(self) -> &'static str {
        self.method.tag()
    }

    /// One sentence naming what was re-run, on what, and what that is worth.
    #[must_use]
    pub const fn explanation(self) -> &'static str {
        match self.method {
            CorroborationMethod::StandaloneTautology => {
                "every deferred clause was re-decided by AY's own decision procedures, as a standalone theory tautology or as entailed by the authored problem (evidence E1: re-derived by AY, not an external check)"
            }
            CorroborationMethod::Resolve => {
                "a fresh Executor running the same code re-decided the authored obligation as unsat (evidence E1: a reproduction, not an independent check)"
            }
            CorroborationMethod::Entailment => {
                "a fresh Executor running the same code re-decided that the authored obligation entails every deferred clause, and every other proof step was strictly validated (evidence E1: the deferred clauses were reproduced, not checked)"
            }
        }
    }
}

/// The evidence behind one `unsat`: its level and, for a refutation admitted
/// on a deferred-trust discharge, what corroborated it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnsatEvidence {
    level: UnsatEvidenceLevel,
    corroboration: Option<UnsatCorroboration>,
}

impl UnsatEvidence {
    /// A refutation a checker verified.
    pub(crate) const CHECKED: Self = Self {
        level: UnsatEvidenceLevel::E2,
        corroboration: None,
    };
    /// A checked refutation resting on premises AY re-derived itself.
    pub(crate) const RE_DERIVED: Self = Self {
        level: UnsatEvidenceLevel::E1,
        corroboration: None,
    };
    /// No checked refutation.
    pub(crate) const RAW: Self = Self {
        level: UnsatEvidenceLevel::E0,
        corroboration: None,
    };

    /// A refutation admitted on a deferred-trust discharge.
    pub(crate) const fn corroborated(corroboration: UnsatCorroboration) -> Self {
        Self {
            level: UnsatEvidenceLevel::E1,
            corroboration: Some(corroboration),
        }
    }

    /// The evidence level.
    #[must_use]
    pub const fn level(self) -> UnsatEvidenceLevel {
        self.level
    }

    /// The corroboration, when the refutation rests on one.
    #[must_use]
    pub const fn corroboration(self) -> Option<UnsatCorroboration> {
        self.corroboration
    }

    /// The same evidence, seen from the theorem that sealed it.
    #[must_use]
    pub(crate) const fn nested(self, source: CorroborationSource) -> Self {
        match self.corroboration {
            Some(corroboration) => Self::corroborated(corroboration.nested(source)),
            None => self,
        }
    }

    /// The weaker of two pieces of evidence: a theorem that seals several
    /// refutations is exactly as strong as the weakest one. On a tie the first
    /// corroboration is kept, so a composite always names one.
    #[must_use]
    pub(crate) const fn weakest(self, other: Self) -> Self {
        let level = if (other.level as u8) < (self.level as u8) {
            other.level
        } else {
            self.level
        };
        let corroboration = match (self.corroboration, other.corroboration) {
            (Some(corroboration), _) | (None, Some(corroboration)) => Some(corroboration),
            (None, None) => None,
        };
        Self {
            level,
            corroboration,
        }
    }
}

#[cfg(test)]
#[path = "corroboration_tests.rs"]
mod tests;
