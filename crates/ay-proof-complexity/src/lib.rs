#![forbid(unsafe_code)]
#![warn(missing_docs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof Complexity Analysis Tools
//!
//! This crate provides tools for analyzing proof complexity, including:
//!
//! - **Hard formula generators**: Pigeonhole, Tseitin, random k-CNF, parity
//! - **Proof systems**: Resolution, Tree Resolution, Extended Resolution, Frege, etc.
//! - **Proof analysis**: Size bounds, width bounds, proof verification
//!
//! ## Hard Formulas
//!
//! Hard formulas are CNF formulas that are known to require exponential-size proofs
//! in certain proof systems. They are useful for:
//!
//! - Testing SAT solver performance
//! - Understanding proof complexity
//! - Benchmarking proof search algorithms
//!
//! ### Pigeonhole Principle (PHP)
//!
//! The pigeonhole principle states that n+1 pigeons cannot fit into n holes
//! if each pigeon must occupy exactly one hole. This is easy to prove for humans
//! but requires exponential-size resolution proofs.
//!
//! ```
//! use ay_proof_complexity::pigeonhole;
//!
//! // PHP with 4 pigeons and 3 holes (unsatisfiable)
//! let formula = pigeonhole(3);
//! // This requires exponential-size resolution proof to refute
//! ```
//!
//! ### Tseitin Formulas
//!
//! Tseitin formulas encode XOR constraints on a graph. They are hard for
//! tree-resolution but easy for general resolution with extension variables.
//!
//! ### Random k-CNF
//!
//! Random k-CNF formulas near the satisfiability threshold are challenging
//! for most SAT solvers.
//!
//! ## Proof Systems
//!
//! This crate supports analysis of various propositional proof systems:
//!
//! - **Resolution**: Clause learning (what CDCL SAT solvers produce)
//! - **Tree Resolution**: Resolution where proof is a tree (no clause reuse)
//! - **Regular Resolution**: Each variable resolved at most once per path
//! - **Extended Resolution**: Resolution with auxiliary variables
//! - **Frege**: Standard propositional logic proofs
//! - **Extended Frege**: Frege with abbreviations
//!
//! ## References
//!
//! - Krajicek, "Proof Complexity"
//! - Cook & Reckhow, "The Relative Efficiency of Propositional Proof Systems"
//! - Beame & Pitassi, "Propositional Proof Complexity: Past, Present, and Future"
//! - Haken, "The Intractability of Resolution" (1985) - PHP lower bound

pub(crate) mod cnf;
pub mod corpus;
pub mod features;
mod graph;
pub(crate) mod graph_formulas;
pub(crate) mod hard_formulas;
pub mod obligation;
pub(crate) mod proof_systems;

pub(crate) use ay_sat::Literal as Lit;
pub(crate) use ay_sat::Variable as Var;

pub use cnf::Cnf;
pub use corpus::{generate_default_corpus, CorpusEntry};
pub use features::ProofComplexityFeatures;
pub use graph::Graph;
pub use graph_formulas::{clique_coloring, graph_coloring, tseitin};
pub use hard_formulas::{ordering_principle, parity, pigeonhole, random_k_cnf};
pub use obligation::{
    ArtifactRef, BenchmarkTags, EquivalenceSubstitutionLratSlice, FactorExtensionLratDryRun,
    FactorExtensionLratTransaction, FormulaMetadata, ObligationDomainProfile, ObligationGoalKind,
    ProofMetadata, SatPbProofObligation, TrustPolicy, SAT_PB_OBLIGATION_SCHEMA_VERSION,
};
pub use proof_systems::{
    Clause, ProofSystem, ResolutionProof, ResolutionProofError, ResolutionStep,
};
