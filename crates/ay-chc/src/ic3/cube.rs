// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cube and frame types for clause-level IC3 (#8211).

use ay_sat::Literal;
use std::cmp::Ordering;
use std::rc::Rc;

/// A cube: conjunction of state-variable literals.
///
/// In clause-level IC3, a cube represents a (partial) state. Blocking a cube
/// means adding its negation (a clause) to the frame.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Cube {
    pub(crate) literals: Vec<Literal>,
}

impl Cube {
    /// Create a new cube from a list of literals.
    pub(crate) fn new(literals: Vec<Literal>) -> Self {
        Self { literals }
    }

    /// Number of literals in the cube.
    pub(crate) fn len(&self) -> usize {
        self.literals.len()
    }

    /// Negate the cube to produce a blocking clause.
    /// cube = (l1 AND l2 AND l3) => clause = (NOT l1 OR NOT l2 OR NOT l3)
    pub(crate) fn to_clause(&self) -> Vec<Literal> {
        self.literals.iter().map(|&lit| lit.negated()).collect()
    }
}

/// A single frame in the IC3 frame sequence.
///
/// Frame F_i over-approximates the states reachable in at most i steps.
/// It is represented as a conjunction of clauses (each clause blocks a set
/// of states). Frame monotonicity: F_i => F_{i+1} (states grow), which means
/// blocking clauses hold at SMALLER levels (F_i is tighter than F_{i+1}).
///
/// # Delta encoding (#8672 Finding #1)
///
/// Each blocking clause is stored at exactly ONE frame — the HIGHEST level
/// at which it has been proven to hold. The logical contents of F_i are:
///
/// ```text
/// F_i := Init ∧ ⋃_{j >= i} frames[j].blocked_clauses
/// ```
///
/// This matches Z3 Spacer's `spacer_legacy_frames.cpp::propagate_to_next_level`
/// (reference/z3/src/muz/spacer/spacer_legacy_frames.cpp:75-121), where a
/// propagated lemma is removed from its source level (`src.pop_back()`) and
/// re-added at the higher target level.
///
/// Before this fix, each lemma was stored in every frame 1..=level, giving
/// O(lemmas * depth) memory growth. Delta encoding gives O(lemmas).
#[derive(Debug)]
pub(crate) struct Ic3Frame {
    /// Blocking clauses whose highest confirmed level is THIS frame.
    ///
    /// With delta encoding, a clause appears in exactly one frame's
    /// `blocked_clauses`. To enumerate F_i, walk frames[j] for j >= i.
    pub(crate) blocked_clauses: Vec<Vec<Literal>>,
    /// Activation literal for this frame in the shared SAT solver.
    /// When asserting F_i's constraints in a SAT query, we assume the
    /// activation literals of frames i, i+1, ..., last (see solver.rs
    /// `collect_frame_activations`). A blocking clause added at frame j is
    /// asserted as `(¬frames[j].activation ∨ clause)` in the SAT solver.
    pub(crate) activation: Literal,
}

impl Ic3Frame {
    /// Create a new empty frame with the given activation literal.
    pub(crate) fn new(activation: Literal) -> Self {
        Self {
            blocked_clauses: Vec::new(),
            activation,
        }
    }

    /// Add a blocking clause (negated cube) to this frame.
    pub(crate) fn add_blocked_clause(&mut self, clause: Vec<Literal>) {
        self.blocked_clauses.push(clause);
    }

    /// Number of blocking clauses stored at THIS frame's level.
    ///
    /// Under delta encoding this is NOT the total size of F_i — to get
    /// the total constraint count at level i, sum `num_clauses()` over
    /// frames j for j >= i.
    pub(crate) fn num_clauses(&self) -> usize {
        self.blocked_clauses.len()
    }
}

/// A proof obligation for the IC3 solver.
///
/// Represents a cube that needs to be blocked at a given frame level.
/// The priority queue processes obligations with lower levels first.
#[derive(Debug, Clone)]
pub(crate) struct Ic3Obligation {
    /// The cube to block (conjunction of state-variable literals)
    pub(crate) cube: Cube,
    /// Frame level at which to block this cube
    pub(crate) level: usize,
    /// Depth in the obligation tree (for counterexample reconstruction)
    pub(crate) depth: usize,
    /// Monotonic sequence ID for deterministic tie-breaking
    pub(crate) seq_id: u64,
    /// Parent obligation in the predecessor chain (for counterexample
    /// reconstruction). The parent obligation is the cube at a HIGHER
    /// frame level that this obligation is a predecessor of. Walking
    /// parent links from a level-0 obligation up to the original bad
    /// cube yields the full Init → Bad trace.
    pub(crate) parent: Option<Rc<Self>>,
}

impl Ic3Obligation {
    pub(crate) fn new(
        cube: Cube,
        level: usize,
        depth: usize,
        seq_id: u64,
        parent: Option<Rc<Self>>,
    ) -> Self {
        Self {
            cube,
            level,
            depth,
            seq_id,
            parent,
        }
    }
}

/// Wrapper for BinaryHeap ordering: lower level = higher priority.
#[derive(Debug)]
pub(crate) struct PriorityObligation(pub(crate) Ic3Obligation);

impl PartialEq for PriorityObligation {
    fn eq(&self, other: &Self) -> bool {
        self.0.level == other.0.level && self.0.seq_id == other.0.seq_id
    }
}

impl Eq for PriorityObligation {}

impl PartialOrd for PriorityObligation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PriorityObligation {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse: lower level comes first from max-heap
        other
            .0
            .level
            .cmp(&self.0.level)
            .then_with(|| other.0.seq_id.cmp(&self.0.seq_id))
    }
}
