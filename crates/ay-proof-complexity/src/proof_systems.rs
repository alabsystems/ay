// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Propositional proof systems for proof complexity analysis.
//!
//! This module provides representations and verification for various
//! propositional proof systems.

use crate::{Lit, Var};
use ay_core::kani_compat::DetHashSet as HashSet;
use thiserror::Error;

/// Errors that can be reported by [`ResolutionProof::verify`].
///
/// The variants carry the failing step index and enough structural context
/// to diagnose malformed proofs without panicking on untrusted input.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum ResolutionProofError {
    /// A resolution step references a parent index that is not strictly
    /// less than the step's own index.
    #[error(
        "step {step}: parent index out of bounds (parent1={parent1}, parent2={parent2} must be < {step})"
    )]
    ParentOutOfBounds {
        /// Index of the step whose parents are invalid.
        step: usize,
        /// Reported first parent index.
        parent1: usize,
        /// Reported second parent index.
        parent2: usize,
    },
    /// A resolution step references a parent index that does not correspond
    /// to any recorded proof step. This is reported instead of panicking on
    /// malformed `parent1`/`parent2` fields.
    #[error("step {step}: missing parent clause at index {parent} (proof length {len})")]
    MissingParent {
        /// Index of the step whose parent lookup failed.
        step: usize,
        /// Missing parent index.
        parent: usize,
        /// Total number of steps in the proof.
        len: usize,
    },
    /// The pivot literal does not appear with opposite polarity in the two
    /// parent clauses, so the step is not a valid resolution.
    #[error("step {step}: pivot variable {pivot:?} not present with opposite polarity in parents")]
    PivotNotResolved {
        /// Index of the step.
        step: usize,
        /// Pivot variable that failed the polarity check.
        pivot: Var,
    },
    /// The recorded clause does not match the resolvent derived from the
    /// parents on the pivot literal.
    #[error("step {step}: recorded clause does not match expected resolvent")]
    ResolventMismatch {
        /// Index of the step.
        step: usize,
        /// Recorded clause.
        recorded: Clause,
        /// Expected resolvent (sorted, deduplicated).
        expected: Clause,
    },
}

/// Propositional proof systems ordered by strength.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProofSystem {
    /// Tree-like Resolution (no clause reuse)
    TreeResolution,
    /// Regular Resolution (each variable resolved at most once per path)
    RegularResolution,
    /// General Resolution (CDCL produces these)
    Resolution,
    /// Extended Resolution (with auxiliary variables)
    ExtendedResolution,
    /// Frege systems (standard propositional logic)
    Frege,
    /// Extended Frege (Frege with abbreviations)
    ExtendedFrege,
    /// Cutting Planes (integer linear programming proofs)
    CuttingPlanes,
    /// Polynomial Calculus
    PolynomialCalculus,
    /// Sum of Squares (SOS)
    SumOfSquares,
}

impl ProofSystem {
    /// Returns true if this system p-simulates the other.
    ///
    /// System A p-simulates system B if any proof in B can be converted
    /// to a proof in A with at most polynomial blowup.
    pub fn p_simulates(&self, other: &Self) -> bool {
        use ProofSystem::{
            CuttingPlanes, ExtendedFrege, ExtendedResolution, Frege, RegularResolution, Resolution,
            TreeResolution,
        };
        match (self, other) {
            // Same system always simulates itself
            (a, b) if a == b => true,

            // Simulation hierarchy (nested or-patterns grouped by simulated system)
            (
                Resolution | RegularResolution | ExtendedResolution | CuttingPlanes,
                TreeResolution,
            )
            | (Resolution | ExtendedResolution, RegularResolution)
            | (ExtendedResolution | Frege, Resolution)
            | (ExtendedFrege, Frege | ExtendedResolution) => true,

            // Default: we don't know, it doesn't simulate, or it's an open problem
            // Note: (Frege, ExtendedResolution) is an open problem
            _ => false,
        }
    }

    /// Known exponential lower bounds for this proof system.
    pub fn known_lower_bounds(&self) -> &'static [&'static str] {
        use ProofSystem::{
            CuttingPlanes, ExtendedFrege, ExtendedResolution, Frege, PolynomialCalculus,
            RegularResolution, Resolution, SumOfSquares, TreeResolution,
        };
        match self {
            TreeResolution => &[
                "Pigeonhole (PHP) - exponential",
                "Tseitin on expanders - exponential",
                "Random 3-CNF near threshold - exponential",
                "Parity - exponential",
            ],
            RegularResolution => &[
                "Pigeonhole (PHP) - exponential",
                "Tseitin on expanders - exponential",
            ],
            Resolution => &[
                "Pigeonhole (PHP) - exponential (Haken 1985)",
                "Tseitin on expanders - exponential (Urquhart 1987)",
                "Random 3-CNF - exponential (Chvatal-Szemeredi 1988)",
            ],
            ExtendedResolution => &[
                "No exponential lower bounds known!",
                "PHP has polynomial proofs (Cook 1976)",
            ],
            Frege | ExtendedFrege => &["No super-polynomial lower bounds known!"],
            CuttingPlanes => &[
                "Random CNF - exponential (Pudlak 1997)",
                "Clique-coloring - exponential",
            ],
            PolynomialCalculus => &[
                "Pigeonhole - degree lower bound (Razborov 1998)",
                "Tseitin - degree lower bound",
            ],
            SumOfSquares => &["Random 3-XOR - degree lower bound (Grigoriev-Vorobjov 2001)"],
        }
    }
}

/// A clause in a resolution proof.
pub type Clause = Vec<Lit>;

/// A step in a resolution proof.
#[derive(Debug, Clone)]
pub enum ResolutionStep {
    /// Axiom (original clause from the formula)
    Axiom(Clause),
    /// Resolution: derive C from clauses at indices i and j by resolving on variable
    Resolve {
        /// Clause derived by resolving `parent1` and `parent2`.
        clause: Clause,
        /// Index of the first parent clause in the proof.
        parent1: usize,
        /// Index of the second parent clause in the proof.
        parent2: usize,
        /// Pivot variable eliminated during the resolution step.
        pivot: Var,
    },
}

impl ResolutionStep {
    /// Get the clause from this step (axiom clause or derived clause).
    pub fn clause(&self) -> &Clause {
        match self {
            Self::Axiom(c) => c,
            Self::Resolve { clause, .. } => clause,
        }
    }
}

/// A resolution proof.
#[derive(Debug, Clone)]
pub struct ResolutionProof {
    /// Steps of the proof
    steps: Vec<ResolutionStep>,
}

impl ResolutionProof {
    /// Create a new empty proof.
    pub fn new() -> Self {
        Self { steps: Vec::new() }
    }

    /// Add an axiom (original clause).
    pub fn add_axiom(&mut self, clause: Clause) -> usize {
        let idx = self.steps.len();
        self.steps.push(ResolutionStep::Axiom(clause));
        idx
    }

    /// Add a resolution step.
    pub fn add_resolution(
        &mut self,
        clause: Clause,
        parent1: usize,
        parent2: usize,
        pivot: Var,
    ) -> usize {
        let idx = self.steps.len();
        self.steps.push(ResolutionStep::Resolve {
            clause,
            parent1,
            parent2,
            pivot,
        });
        idx
    }

    /// Number of steps in the proof.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Check if proof is empty.
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Get the clause at a given step.
    pub fn clause_at(&self, idx: usize) -> Option<&Clause> {
        Some(self.steps.get(idx)?.clause())
    }

    /// Check if this is a valid refutation (derives empty clause).
    pub fn is_refutation(&self) -> bool {
        self.steps.last().is_some_and(|s| s.clause().is_empty())
    }

    /// Verify the proof is valid.
    ///
    /// Checks that each resolution step correctly derives its clause
    /// from its parents by resolving on the pivot variable. Returns a
    /// typed [`ResolutionProofError`] describing the failing step if the
    /// proof is malformed; never panics on untrusted input.
    pub fn verify(&self) -> Result<(), ResolutionProofError> {
        let len = self.steps.len();
        for (idx, step) in self.steps.iter().enumerate() {
            match step {
                ResolutionStep::Axiom(_) => {
                    // Axioms are always valid
                }
                ResolutionStep::Resolve {
                    clause,
                    parent1,
                    parent2,
                    pivot,
                } => {
                    // Check parent indices are valid
                    if *parent1 >= idx || *parent2 >= idx {
                        return Err(ResolutionProofError::ParentOutOfBounds {
                            step: idx,
                            parent1: *parent1,
                            parent2: *parent2,
                        });
                    }

                    // Get parent clauses without panicking on malformed input
                    let c1 =
                        self.clause_at(*parent1)
                            .ok_or(ResolutionProofError::MissingParent {
                                step: idx,
                                parent: *parent1,
                                len,
                            })?;
                    let c2 =
                        self.clause_at(*parent2)
                            .ok_or(ResolutionProofError::MissingParent {
                                step: idx,
                                parent: *parent2,
                                len,
                            })?;

                    // Check pivot appears positive in one and negative in other
                    let pos_pivot = Lit::positive(*pivot);
                    let neg_pivot = Lit::negative(*pivot);

                    let (pos_parent, neg_parent) =
                        if c1.contains(&pos_pivot) && c2.contains(&neg_pivot) {
                            (c1, c2)
                        } else if c1.contains(&neg_pivot) && c2.contains(&pos_pivot) {
                            (c2, c1)
                        } else {
                            return Err(ResolutionProofError::PivotNotResolved {
                                step: idx,
                                pivot: *pivot,
                            });
                        };

                    // Compute expected resolvent
                    let mut expected: Vec<Lit> = pos_parent
                        .iter()
                        .filter(|&&l| l != pos_pivot)
                        .chain(neg_parent.iter().filter(|&&l| l != neg_pivot))
                        .copied()
                        .collect();
                    expected.sort_by_key(|l| (l.variable().index(), !l.is_positive()));
                    expected.dedup();

                    // Check clause matches expected
                    let mut actual = clause.clone();
                    actual.sort_by_key(|l| (l.variable().index(), !l.is_positive()));

                    if actual != expected {
                        return Err(ResolutionProofError::ResolventMismatch {
                            step: idx,
                            recorded: actual,
                            expected,
                        });
                    }
                }
            }
        }
        Ok(())
    }

    /// Check if this is a tree resolution proof (no clause reuse).
    pub fn is_tree(&self) -> bool {
        let mut used = vec![false; self.steps.len()];

        for step in &self.steps {
            if let ResolutionStep::Resolve {
                parent1, parent2, ..
            } = step
            {
                if used[*parent1] || used[*parent2] {
                    return false;
                }
                used[*parent1] = true;
                used[*parent2] = true;
            }
        }
        true
    }

    /// Check if this is a regular resolution proof.
    ///
    /// A proof is regular if on every path from root to axiom,
    /// each variable is resolved on at most once.
    pub fn is_regular(&self) -> bool {
        // For each step, track which variables have been resolved on the path to it
        let mut resolved_on_path: Vec<HashSet<Var>> = vec![HashSet::default(); self.steps.len()];

        for (idx, step) in self.steps.iter().enumerate() {
            if let ResolutionStep::Resolve {
                parent1,
                parent2,
                pivot,
                ..
            } = step
            {
                // Union of variables resolved on paths to parents, plus this pivot
                let mut vars = resolved_on_path[*parent1].clone();
                let mut parent2_vars: Vec<_> = resolved_on_path[*parent2].iter().copied().collect();
                parent2_vars.sort_unstable();
                vars.extend(parent2_vars);

                if vars.contains(pivot) {
                    return false;
                }
                vars.insert(*pivot);
                resolved_on_path[idx] = vars;
            }
        }
        true
    }

    /// Width of the proof (maximum clause size).
    pub fn width(&self) -> usize {
        self.steps
            .iter()
            .map(|step| step.clause().len())
            .max()
            .unwrap_or(0)
    }

    /// Space of the proof (maximum number of clauses needed at once).
    ///
    /// This is a lower bound computed by analyzing clause lifetimes.
    pub fn space(&self) -> usize {
        let n = self.steps.len();
        if n == 0 {
            return 0;
        }

        // For each step, compute when it's last used
        let mut last_use = vec![0usize; n];
        for (idx, step) in self.steps.iter().enumerate() {
            if let ResolutionStep::Resolve {
                parent1, parent2, ..
            } = step
            {
                last_use[*parent1] = idx;
                last_use[*parent2] = idx;
            }
        }

        // Simulate proof and track max clauses alive
        let mut alive = 0usize;
        let mut max_alive = 0usize;

        for idx in 0..n {
            alive += 1; // New clause derived
            max_alive = max_alive.max(alive);

            // Check if any clause dies at this step
            for (prev, &usage) in last_use.iter().enumerate().take(idx + 1) {
                if usage == idx && prev != idx {
                    alive = alive.saturating_sub(1);
                }
            }
        }

        max_alive
    }
}

impl Default for ResolutionProof {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
#[path = "proof_systems_tests.rs"]
mod tests;
