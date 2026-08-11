// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory-attributed UNSAT core types.
//!
//! Provides [`AnnotatedUnsatCore`], which enriches a standard UNSAT core
//! with per-literal theory attribution.  Each literal in the core is tagged
//! with the theory (or theories) responsible for its contribution to the
//! UNSAT proof, along with theory-specific certificates:
//!
//! - **LRA/LIA:** Farkas coefficients witnessing the linear infeasibility.
//! - **EUF:** Congruence chains linking the conflicting equality/disequality.
//! - **BV / Strings / Datatypes:** Bit-blasting or axiom provenance.
//!
//! # Design
//!
//! The core is extracted from the solver's internal proof object after an
//! UNSAT result.  Theory lemma steps in the proof carry `TheoryLemmaKind`
//! and optional `FarkasAnnotation` / `LiaAnnotation`.  We walk the proof
//! DAG, collect theory lemma attributions, and map them back to the named
//! assertions in the UNSAT core.
//!
//! Part of #8153 (Phase 5 Explainability).

use ay_core::term::{Symbol, TermData};
use ay_core::{LiaAnnotation, TermId, TermStore, TheoryLemmaKind};
use num_rational::Rational64;

use super::Term;

/// How a quantifier was instantiated.
///
/// Records the mechanism that produced a ground instance of a quantified
/// formula.  This is useful for proof explanation: users can see whether an
/// instance came from pattern-based E-matching, counterexample-guided
/// instantiation, or another strategy.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum InstantiationMethod {
    /// E-matching: a trigger pattern matched ground terms in the current
    /// E-graph, producing a substitution for the quantified variables.
    EMatching,
    /// Counterexample-Guided Quantifier Instantiation: the solver found a
    /// model that violates the quantified formula and used it to derive a
    /// ground instance.
    Cegqi,
    /// Model-Based Quantifier Instantiation: a candidate model is used to
    /// select representative ground terms for instantiation.
    Mbqi,
    /// Skolemization: the quantifier was eliminated by introducing fresh
    /// Skolem functions/constants.
    Skolemization,
}

/// A single step in an EUF congruence chain.
///
/// Records that `left = right` was established by the given `reason`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CongruenceStep {
    /// Left-hand side of the equality.
    pub left: Term,
    /// Right-hand side of the equality.
    pub right: Term,
    /// Why these terms are equal.
    pub reason: CongruenceReason,
}

/// How an EUF equality was established.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CongruenceReason {
    /// Direct assertion: `(= a b)` was asserted.
    Direct,
    /// Congruence closure: `f(a1,...,an) = f(b1,...,bn)` because each `ai = bi`.
    Congruence,
    /// Shared equality from Nelson-Oppen theory combination.
    Shared,
    /// ITE axiom: `ite(c,t,e) = t` when `c` is true (or `e` when false).
    Ite,
    /// Both endpoints share the same Boolean truth value.
    BoolValue,
}

/// Theory-specific certificate attached to a core literal.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum TheoryAttribution {
    /// Linear arithmetic (LRA or LIA): Farkas certificate.
    ///
    /// The coefficients witness that a non-negative linear combination of
    /// the core constraints yields a contradiction (0 >= 1 or similar).
    /// Each entry pairs a core literal index with its Farkas coefficient.
    Farkas {
        /// Farkas coefficients, one per literal in this conflict.
        coefficients: Vec<Rational64>,
    },

    /// LIA-specific certificate with additional integrality reasoning.
    LiaGeneric {
        /// Farkas coefficients (if available).
        coefficients: Option<Vec<Rational64>>,
        /// Kind of LIA reasoning (bounds gap, GCD, Gomory, etc.).
        lia_kind: String,
    },

    /// EUF: congruence chain explaining why two terms are equal.
    EufTransitive {
        /// The chain of equalities from left to right.
        chain: Vec<CongruenceStep>,
    },

    /// EUF congruence: `f(a) = f(b)` because `a = b`.
    EufCongruent {
        /// The chain of argument equalities.
        chain: Vec<CongruenceStep>,
    },

    /// Bitvector bit-blasting.
    BvBitBlast,

    /// String theory axiom.
    StringAxiom,

    /// Datatype theory axiom.
    DatatypeAxiom,

    /// Quantifier instantiation: a ground instance of a universally quantified
    /// formula was derived and added to the solver.
    ///
    /// Records the source quantifier, the trigger pattern that matched (if
    /// E-matching was used), the ground substitution, and the instantiation
    /// method.
    QuantifierInstantiation {
        /// The quantified formula that was instantiated.
        quantifier: Term,
        /// The trigger pattern that matched (for E-matching).
        ///
        /// `None` when the instantiation method does not use triggers
        /// (e.g., CEGQI, MBQI).
        trigger: Option<Vec<Term>>,
        /// Ground substitution mapping each bound variable name to the
        /// concrete term it was replaced with.
        substitution: Vec<(String, Term)>,
        /// How the instantiation was produced.
        method: InstantiationMethod,
    },

    /// Generic theory lemma without detailed attribution.
    Generic {
        /// Name of the originating theory.
        theory: String,
    },
}

/// A single entry in an annotated UNSAT core.
///
/// Maps a named assertion to the theory attribution(s) explaining its
/// role in the UNSAT proof.
#[derive(Debug, Clone, PartialEq)]
pub struct AnnotatedCoreLiteral {
    /// The assertion name (from `(! ... :named ...)` annotations).
    pub name: String,
    /// Theory attributions for this literal.
    ///
    /// A literal may participate in multiple theory lemmas (e.g., an
    /// equality used in both EUF congruence and LRA bound reasoning).
    pub attributions: Vec<TheoryAttribution>,
}

/// An UNSAT core enriched with theory-level attribution.
///
/// After `check_sat()` returns `Unsat`, call
/// [`Solver::annotated_unsat_core()`](crate::api::Solver::annotated_unsat_core)
/// to obtain a core where each literal carries theory-specific certificates.
///
/// # Requirements
///
/// - `:produce-proofs` must be enabled (proof data is needed to extract
///   theory attributions).
/// - `:produce-unsat-cores` must be enabled (named assertions are needed
///   to map core literals to assertion names).
///
/// # Example
///
/// ```no_run
/// # use ay_dpll::api::{Solver, Sort, Logic, SolveResult};
/// let mut solver = Solver::new(Logic::QfLia);
/// solver.set_produce_proofs(true);
/// solver.set_produce_unsat_cores(true);
/// // ... assert named constraints ...
/// if solver.check_sat().is_unsat() {
///     if let Some(core) = solver.annotated_unsat_core() {
///         for entry in core.entries() {
///             println!("{}: {:?}", entry.name, entry.attributions);
///         }
///     }
/// }
/// ```
#[derive(Debug, Clone)]
pub struct AnnotatedUnsatCore {
    /// The annotated core entries.
    entries: Vec<AnnotatedCoreLiteral>,
    /// Summary of theories involved.
    theories_involved: Vec<String>,
}

impl AnnotatedUnsatCore {
    /// Create a new annotated UNSAT core.
    pub(crate) fn new(entries: Vec<AnnotatedCoreLiteral>, theories_involved: Vec<String>) -> Self {
        Self {
            entries,
            theories_involved,
        }
    }

    /// The annotated core entries.
    #[must_use]
    pub fn entries(&self) -> &[AnnotatedCoreLiteral] {
        &self.entries
    }

    /// Consume and return the annotated core entries.
    #[must_use]
    pub fn into_entries(self) -> Vec<AnnotatedCoreLiteral> {
        self.entries
    }

    /// Names of theories that contributed to the UNSAT proof.
    #[must_use]
    pub fn theories_involved(&self) -> &[String] {
        &self.theories_involved
    }

    /// Number of entries in the core.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the core is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Look up a core entry by assertion name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&AnnotatedCoreLiteral> {
        self.entries.iter().find(|e| e.name == name)
    }

    /// Check whether a particular theory contributed to the core.
    #[must_use]
    pub fn involves_theory(&self, theory: &str) -> bool {
        self.theories_involved.iter().any(|t| t == theory)
    }
}

impl std::fmt::Display for InstantiationMethod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EMatching => write!(f, "E-matching"),
            Self::Cegqi => write!(f, "CEGQI"),
            Self::Mbqi => write!(f, "MBQI"),
            Self::Skolemization => write!(f, "Skolemization"),
        }
    }
}

impl std::fmt::Display for CongruenceReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Direct => write!(f, "direct assertion"),
            Self::Congruence => write!(f, "congruence closure"),
            Self::Shared => write!(f, "Nelson-Oppen shared equality"),
            Self::Ite => write!(f, "ITE axiom"),
            Self::BoolValue => write!(f, "Boolean value"),
        }
    }
}

impl std::fmt::Display for CongruenceStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} = {:?} ({})", self.left, self.right, self.reason)
    }
}

impl std::fmt::Display for TheoryAttribution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Farkas { coefficients } => {
                let n = coefficients.len();
                let noun = if n == 1 {
                    "coefficient"
                } else {
                    "coefficients"
                };
                write!(f, "LRA Farkas ({n} {noun})")
            }
            Self::LiaGeneric {
                coefficients,
                lia_kind,
            } => {
                if let Some(c) = coefficients {
                    let n = c.len();
                    let noun = if n == 1 {
                        "coefficient"
                    } else {
                        "coefficients"
                    };
                    write!(f, "LIA {lia_kind} ({n} {noun})")
                } else {
                    write!(f, "LIA {lia_kind}")
                }
            }
            Self::EufTransitive { chain } => {
                let n = chain.len();
                let noun = if n == 1 { "step" } else { "steps" };
                write!(f, "EUF transitivity ({n} {noun})")
            }
            Self::EufCongruent { chain } => {
                let n = chain.len();
                let noun = if n == 1 { "step" } else { "steps" };
                write!(f, "EUF congruence ({n} {noun})")
            }
            Self::BvBitBlast => write!(f, "BV bit-blasting"),
            Self::StringAxiom => write!(f, "String axiom"),
            Self::DatatypeAxiom => write!(f, "Datatype axiom"),
            Self::QuantifierInstantiation {
                substitution,
                method,
                ..
            } => {
                let n = substitution.len();
                let noun = if n == 1 { "binding" } else { "bindings" };
                write!(f, "Quantifier instantiation ({method}, {n} {noun})")
            }
            Self::Generic { theory } => write!(f, "{theory} (generic)"),
        }
    }
}

impl std::fmt::Display for AnnotatedCoreLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        if self.attributions.is_empty() {
            write!(f, " (no theory attribution)")
        } else {
            write!(f, " [")?;
            for (i, attr) in self.attributions.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{attr}")?;
            }
            write!(f, "]")
        }
    }
}

impl std::fmt::Display for AnnotatedUnsatCore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "AnnotatedUnsatCore({} entries, theories: [{}])",
            self.entries.len(),
            self.theories_involved.join(", "),
        )
    }
}

/// Extract an EUF congruence/transitivity chain from a theory lemma clause.
///
/// An EUF transitivity clause looks like:
///   `(not (= a b)), (not (= b c)), ..., (= a z)`
///
/// Negated equalities are premises (Direct steps), positive equalities are
/// conclusions (Congruence steps for `EufCongruent`, Direct for `EufTransitive`).
///
/// For congruence lemmas (`EufCongruent` / `EufCongruentPred`), the positive
/// literal at the end is a congruence conclusion: `f(a1,...) = f(b1,...)`.
pub(crate) fn extract_euf_chain(
    clause: &[TermId],
    terms: &TermStore,
    is_congruence: bool,
    wrap_term: &impl Fn(TermId) -> Term,
) -> Vec<CongruenceStep> {
    let mut chain = Vec::with_capacity(clause.len());

    for &lit in clause {
        let term_data = terms.get(lit);
        match term_data {
            // Negated equality: ¬(= lhs rhs) — a premise
            TermData::Not(inner) => {
                if let TermData::App(Symbol::Named(name), args) = terms.get(*inner) {
                    if name == "=" && args.len() == 2 {
                        chain.push(CongruenceStep {
                            left: wrap_term(args[0]),
                            right: wrap_term(args[1]),
                            reason: CongruenceReason::Direct,
                        });
                    }
                }
            }
            // Positive equality: (= lhs rhs) — a conclusion
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                let reason = if is_congruence {
                    CongruenceReason::Congruence
                } else {
                    CongruenceReason::Direct
                };
                chain.push(CongruenceStep {
                    left: wrap_term(args[0]),
                    right: wrap_term(args[1]),
                    reason,
                });
            }
            // For EufCongruentPred, the conclusion may be a positive or negated
            // predicate application (not an equality). Skip non-equality literals.
            _ => {}
        }
    }

    chain
}

/// Convert a `TheoryLemmaKind` to a `TheoryAttribution`.
///
/// For EUF lemma kinds, the `clause` and `terms` parameters are used to
/// extract the congruence/transitivity chain from the proof clause literals.
#[inline]
pub(crate) fn attribution_from_lemma(
    kind: &TheoryLemmaKind,
    farkas: Option<&ay_core::FarkasAnnotation>,
    lia: Option<&LiaAnnotation>,
    theory_name: &str,
    clause: &[TermId],
    terms: &TermStore,
    wrap_term: &impl Fn(TermId) -> Term,
) -> TheoryAttribution {
    match kind {
        TheoryLemmaKind::LraFarkas => {
            if let Some(f) = farkas {
                TheoryAttribution::Farkas {
                    coefficients: f.coefficients.clone(),
                }
            } else {
                TheoryAttribution::Generic {
                    theory: "LRA".to_string(),
                }
            }
        }
        TheoryLemmaKind::LiaGeneric => {
            let lia_kind = lia
                .map(|l| format!("{l:?}"))
                .unwrap_or_else(|| "unknown".to_string());
            TheoryAttribution::LiaGeneric {
                coefficients: farkas.map(|f| f.coefficients.clone()),
                lia_kind,
            }
        }
        TheoryLemmaKind::EufTransitive => TheoryAttribution::EufTransitive {
            chain: extract_euf_chain(clause, terms, false, wrap_term),
        },
        TheoryLemmaKind::EufCongruent | TheoryLemmaKind::EufCongruentPred => {
            TheoryAttribution::EufCongruent {
                chain: extract_euf_chain(clause, terms, true, wrap_term),
            }
        }
        TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. } => {
            TheoryAttribution::BvBitBlast
        }
        _ => TheoryAttribution::Generic {
            theory: theory_name.to_string(),
        },
    }
}
