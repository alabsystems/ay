// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Identifiers the CDCL(T) kernel's plug-in interface shares with theory
//! crates (interface freeze v2; the development design notes, "Freeze v2").
//!
//! They name no SAT type, so a theory crate can use them without depending on
//! ay-sat or on the kernel (`ay-cdclt`). The `TheoryPlugin` trait itself stays
//! in `ay-cdclt`: its `Ctx` lends the kernel's atom table and ay-sat's
//! `SolverContext`, and ay-sat depends on this crate, so moving the trait here
//! would make a cycle.

/// A plug-in's dense handle for one of its atoms (KC3).
///
/// The plug-in chooses it in `internalize_atom`, typically the index of the
/// atom in its own table, and the kernel hands it back on every assignment:
/// the propagation path never looks a term up in a hash map to find the atom.
/// Handles are local to one plug-in inside one engine check.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AtomHandle(pub u32);

impl AtomHandle {
    /// The handle as an index into the plug-in's own table.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// How much work a final check may do (KC8).
///
/// The kernel runs the final check level by level, cheapest first, and moves
/// to the next level only when every plug-in accepts the assignment at the
/// current one. Within a level the plug-ins take turns (no plug-in that keeps
/// producing lemmas can starve the others).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Effort {
    /// Bounded checks that need no search of their own (for example
    /// re-checking the propagation fixpoint).
    Cheap,
    /// The theory's own decision procedure on the full assignment.
    Standard,
    /// Model construction and model-based work (combination candidates,
    /// model-based instantiation).
    Model,
    /// Last resort once everything else accepts (expensive completeness
    /// producers: enumeration, finite-model finding).
    LastCall,
}

impl Effort {
    /// Every level, in the order the kernel runs them.
    pub const ALL: [Self; 4] = [Self::Cheap, Self::Standard, Self::Model, Self::LastCall];

    /// The level's position in [`Self::ALL`].
    #[must_use]
    pub const fn index(self) -> usize {
        match self {
            Self::Cheap => 0,
            Self::Standard => 1,
            Self::Model => 2,
            Self::LastCall => 3,
        }
    }
}

/// A proof rule, append-only and versioned (design §3.6). Reserved: the
/// kernel's hints still name a `TheoryLemmaKind`; the open hint (KC5) will
/// name its rule with this id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RuleId(pub u16);

/// A technique that preserves satisfiability but not equivalence (KC26):
/// symmetry breaking, bounded-domain encodings, cutoffs. A check reports the
/// set active in its worker (Σ) with its answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StrengthenId(pub u32);
