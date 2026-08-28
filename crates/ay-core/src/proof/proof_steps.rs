// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by proof to preserve item paths.

/// Proof annotation for a theory lemma clause in the SAT clause trace (#6031 Phase 4).
///
/// Parallel to `ClausificationProof`: when the SAT clause trace contains an
/// "original" clause that was actually a theory lemma (added via `add_theory_lemma`),
/// this annotation tells `SatProofManager` to emit a `TheoryLemma` proof step
/// instead of the generic `assume + or` pattern.
#[derive(Debug, Clone)]
pub struct TheoryLemmaProof {
    /// The lemma clause in the exact order used when its positional
    /// annotations were produced. SAT watched-literal movement may permute a
    /// traced copy, so consumers must rebind annotations by literal identity
    /// rather than zipping them with the trace order.
    pub clause: Vec<TermId>,
    /// The kind of theory lemma (determines the Alethe rule)
    pub kind: TheoryLemmaKind,
    /// Optional Farkas coefficients for arithmetic theories
    pub farkas: Option<FarkasAnnotation>,
    /// Optional LIA-specific annotation (bounds gap, divisibility, cutting plane)
    pub lia: Option<LiaAnnotation>,
}

/// A proof step (Alethe-compatible)
///
/// `PartialEq`/`Eq` are LITERAL structural equality over every field —
/// added for the strict-check memo's document-identity comparison
/// (`ay-dpll` #strict-walk-memo), which deliberately compares the exact
/// stored document instead of a hash so a stale cache hit is impossible
/// rather than improbable.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
#[non_exhaustive]
pub enum ProofStep {
    /// Input assertion from the problem
    Assume(TermId),
    /// Resolution inference (SAT solver)
    Resolution {
        /// The resolvent clause (result of resolution)
        clause: Vec<TermId>,
        /// Pivot literal (resolved on)
        pivot: TermId,
        /// First clause premise
        clause1: ProofId,
        /// Second clause premise
        clause2: ProofId,
    },

    /// Theory lemma (from theory solver)
    TheoryLemma {
        /// Theory name (e.g., "EUF", "LRA", "LIA", "BV")
        theory: String,
        /// The lemma clause (disjunction of literals)
        clause: Vec<TermId>,
        /// Farkas coefficients for arithmetic theories (LRA/LIA)
        /// Used for Craig interpolation
        farkas: Option<FarkasAnnotation>,
        /// Kind of lemma (determines Alethe rule)
        kind: TheoryLemmaKind,
        /// Optional LIA-specific annotation (bounds gap, divisibility, cutting plane)
        lia: Option<LiaAnnotation>,
    },

    /// Generic proof step (Alethe-style)
    Step {
        /// The rule name (e.g., "trans", "cong", "and", "resolution")
        rule: AletheRule,
        /// The conclusion clause (disjunction of literals)
        clause: Vec<TermId>,
        /// Premise step IDs
        premises: Vec<ProofId>,
        /// Additional arguments (rule-specific)
        args: Vec<TermId>,
    },

    /// Subproof anchor (start of nested proof)
    Anchor {
        /// The step that ends this subproof
        end_step: ProofId,
        /// Variables introduced in this subproof
        variables: Vec<(String, crate::sort::Sort)>,
    },
}
pub use crate::alethe::{
    alethe_rule_requires_premises_or_args, is_checkable_alethe_rule, wire_rule_name, AletheRule,
    CHECKABLE_ALETHE_RULES, UNPROVED_STEP_RULE,
};

/// Proof step identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ProofId(pub u32);

impl std::fmt::Display for ProofId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "t{}", self.0)
    }
}

/// A complete proof (Alethe-compatible)
///
/// `PartialEq`/`Eq` are literal structural equality (see [`ProofStep`]'s
/// derive note).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Proof {
    /// Proof steps
    pub steps: Vec<ProofStep>,
    /// Named step IDs (for assume commands)
    pub named_steps: crate::kani_compat::KaniHashMap<String, ProofId>,
}
