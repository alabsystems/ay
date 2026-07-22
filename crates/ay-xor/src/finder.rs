// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! XOR detection from CNF clauses (xorfinder).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_sat::Literal;

use crate::constraint::XorConstraint;
use crate::VarId;

/// Maximum size of XOR constraints we attempt to recover from CNF.
/// Larger XORs require 2^n clauses to encode, so we limit to keep complexity manageable.
const MAX_XOR_SIZE: usize = 8;

/// Minimum size of XOR constraints worth detecting.
/// Unit clauses (size 1) are already handled efficiently by the SAT solver.
const MIN_XOR_SIZE: usize = 2;

/// Binary clause metadata used to recover near-complete ternary XORs.
#[derive(Debug, Clone, Copy)]
struct BinaryClauseSupport {
    /// Assignment to the two sorted variables that falsifies the binary clause.
    ///
    /// Bit 0 corresponds to the first variable, bit 1 to the second. A set bit
    /// means the falsifying assignment sets that variable to true.
    forbidden_assignment: u8,
}

/// A candidate XOR being assembled from CNF clauses.
///
/// An n-variable XOR `x1 XOR x2 XOR ... XOR xn = rhs` is encoded in CNF as
/// 2^(n-1) clauses. Each clause represents one assignment that violates the XOR.
///
/// This struct tracks which combinations we've found to detect when we have
/// a complete XOR.
#[derive(Debug)]
struct PossibleXor {
    /// Variables in the XOR (sorted by variable ID).
    vars: Vec<VarId>,
    /// Right-hand side of the XOR (computed from first clause).
    rhs: bool,
    /// Bitfield tracking which sign combinations we've found.
    /// For n variables, there are 2^n possible combinations.
    /// Combination i has the j-th variable positive iff bit j is 0.
    found_comb: Vec<bool>,
    /// The clause indices that form this XOR (for potential removal).
    clause_indices: Vec<usize>,
}

/// Complete CNF parity encoding recovered as one XOR constraint.
#[derive(Debug, Clone)]
pub(crate) struct XorDetection {
    /// Recovered XOR constraint.
    pub(crate) constraint: XorConstraint,
    /// Zero-based input clause indices that form the complete parity encoding.
    pub(crate) clause_indices: Vec<usize>,
}

impl PossibleXor {
    /// Create a new possible XOR from an initial clause.
    ///
    /// The clause must be sorted by variable ID.
    fn new(clause: &[Literal]) -> Option<Self> {
        if clause.len() < MIN_XOR_SIZE || clause.len() > MAX_XOR_SIZE {
            return None;
        }

        // Extract variables (sorted)
        let vars: Vec<VarId> = clause.iter().map(|lit| lit.variable().id()).collect();

        // A clause (l0 OR l1 OR ... OR ln) forbids the assignment where all literals are FALSE.
        // If li = xi (positive), then the forbidden assignment has xi = 0.
        // If li = -xi (negative), then the forbidden assignment has xi = 1.
        //
        // We use `which_one` to track which assignment is forbidden:
        // bit i = 1 means the forbidden assignment has xi = 1 (so the literal is negative)
        //
        // For XOR: we determine the RHS by computing the parity of the forbidden assignment.
        // If the forbidden assignment has even parity (even number of 1s), then rhs = 1
        // (because we forbid even-parity assignments).
        // If odd parity, then rhs = 0.
        let mut which_one: u32 = 0;
        for (i, lit) in clause.iter().enumerate() {
            if !lit.is_positive() {
                // Negative literal: forbidden assignment has xi = 1
                which_one |= 1 << i;
            }
        }

        // Compute RHS from the parity of the forbidden assignment
        let forbidden_parity = which_one.count_ones() % 2;
        // If we forbid even parity assignments, XOR rhs = 1
        // If we forbid odd parity assignments, XOR rhs = 0
        let rhs = forbidden_parity == 0;

        // Initialize found_comb bitfield
        let n = vars.len();
        let mut found_comb = vec![false; 1 << n];
        found_comb[which_one as usize] = true;

        Some(Self {
            vars,
            rhs,
            found_comb,
            clause_indices: Vec::new(),
        })
    }

    /// Try to add a clause to this possible XOR.
    ///
    /// Returns true if the clause matches and was added.
    fn try_add(&mut self, clause: &[Literal]) -> bool {
        // Quick size check
        if clause.len() != self.vars.len() {
            return false;
        }

        // Check that variables match
        for (i, lit) in clause.iter().enumerate() {
            if lit.variable().id() != self.vars[i] {
                return false;
            }
        }

        // Compute which forbidden assignment this clause represents
        let mut which_one: u32 = 0;
        for (i, lit) in clause.iter().enumerate() {
            if !lit.is_positive() {
                which_one |= 1 << i;
            }
        }

        // Compute RHS from this clause's forbidden parity
        let forbidden_parity = which_one.count_ones() % 2;
        let this_rhs = forbidden_parity == 0;

        // RHS must match for all clauses in the XOR
        if this_rhs != self.rhs {
            return false;
        }

        // Mark this combination as found
        self.found_comb[which_one as usize] = true;
        true
    }

    /// Check if we have found all required clauses.
    ///
    /// For XOR `x0 XOR x1 XOR ... XOR xn = rhs`:
    /// - If rhs = 1, we need to forbid all assignments with EVEN parity (0, 2, 4, ... ones)
    /// - If rhs = 0, we need to forbid all assignments with ODD parity (1, 3, 5, ... ones)
    fn is_complete(&self) -> bool {
        for (i, &found) in self.found_comb.iter().enumerate() {
            let popcount = (i as u32).count_ones();
            let is_even_parity = popcount.is_multiple_of(2);

            // If rhs = 1, we forbid even parity assignments
            // If rhs = 0, we forbid odd parity assignments
            let should_be_forbidden = if self.rhs {
                is_even_parity
            } else {
                !is_even_parity
            };

            if should_be_forbidden && !found {
                return false;
            }
        }
        true
    }

    /// Return the unique missing forbidden assignment, if exactly one remains.
    fn missing_required_combination(&self) -> Option<usize> {
        let mut missing = None;

        for (i, &found) in self.found_comb.iter().enumerate() {
            let popcount = (i as u32).count_ones();
            let is_even_parity = popcount.is_multiple_of(2);
            let should_be_forbidden = if self.rhs {
                is_even_parity
            } else {
                !is_even_parity
            };

            if should_be_forbidden && !found {
                if missing.is_some() {
                    return None;
                }
                missing = Some(i);
            }
        }

        missing
    }

    /// Detect the common "3 XOR clauses + 1 supporting binary clause" shape.
    ///
    /// In SAT competition parity encodings, a ternary XOR can appear with one of
    /// its four CNF clauses omitted because an extra binary clause already blocks
    /// that missing violating assignment. In that case the ternary clauses plus
    /// the binary clause are equivalent to the full XOR plus the binary clause,
    /// so we can safely recover the XOR and leave the binary clause in CNF.
    fn is_supported_partial_xor(
        &self,
        binary_clauses: &HashMap<(VarId, VarId), Vec<BinaryClauseSupport>>,
    ) -> bool {
        if self.vars.len() != 3 || self.is_complete() {
            return false;
        }

        let Some(missing) = self.missing_required_combination() else {
            return false;
        };

        for (lhs_idx, rhs_idx) in [(0, 1), (0, 2), (1, 2)] {
            let key = (self.vars[lhs_idx], self.vars[rhs_idx]);
            let Some(supports) = binary_clauses.get(&key) else {
                continue;
            };

            let forbidden_assignment =
                (((missing >> lhs_idx) & 1) as u8) | ((((missing >> rhs_idx) & 1) as u8) << 1);

            if supports
                .iter()
                .any(|support| support.forbidden_assignment == forbidden_assignment)
            {
                return true;
            }
        }

        false
    }

    /// Convert to an XorConstraint.
    fn to_constraint(&self) -> XorConstraint {
        XorConstraint {
            vars: self.vars.clone(),
            rhs: self.rhs,
        }
    }
}

/// XOR finder: detects XOR constraints encoded in CNF clauses.
///
/// This module implements the algorithm from CryptoMiniSat to recover
/// XOR constraints from CNF clause databases. An n-variable XOR is
/// encoded as 2^(n-1) clauses, each forbidding one violating assignment.
///
/// # Example
///
/// ```
/// use ay_xor::XorFinder;
/// use ay_sat::{Literal, Variable};
///
/// // CNF encoding of x0 XOR x1 = 1:
/// // (-x0 OR -x1) - forbids (1,1) -> parity 0
/// // (x0 OR x1)   - forbids (0,0) -> parity 0
/// let clauses = vec![
///     vec![Literal::negative(Variable::new(0)), Literal::negative(Variable::new(1))],
///     vec![Literal::positive(Variable::new(0)), Literal::positive(Variable::new(1))],
/// ];
///
/// let mut finder = XorFinder::new();
/// let xors = finder.find_xors(&clauses);
/// assert_eq!(xors.len(), 1);
/// ```
#[derive(Debug, Default)]
pub struct XorFinder {
    /// Candidates grouped by their variable set (as a sorted tuple).
    candidates: HashMap<Vec<VarId>, PossibleXor>,
}

impl XorFinder {
    /// Create a new XOR finder.
    pub fn new() -> Self {
        Self::default()
    }

    /// Find all XOR constraints in a set of clauses.
    ///
    /// Returns the detected XOR constraints. The input clauses that encode
    /// these XORs could potentially be removed from the clause database.
    ///
    /// Detection works by matching the standard CNF parity encoding:
    /// 1. Sort each clause by variable ID and group clauses by their variable set.
    /// 2. Interpret each clause as forbidding exactly one assignment on that set:
    ///    a positive literal means the forbidden assignment sets that variable to
    ///    false, and a negative literal means it sets the variable to true.
    /// 3. A full `x0 XOR x1 XOR ... XOR xn = rhs` encoding is present when we see
    ///    every forbidden assignment whose parity violates `rhs`. That is exactly
    ///    `2^(n - 1)` clauses with a consistent parity class.
    /// 4. For ternary XORs, also accept the common SAT-competition variant where
    ///    one violating assignment is blocked by an extra binary clause instead of
    ///    the fourth ternary clause.
    ///
    /// `MAX_XOR_SIZE` keeps this bounded because the pattern space grows
    /// exponentially with the number of variables.
    pub fn find_xors(&mut self, clauses: &[Vec<Literal>]) -> Vec<XorConstraint> {
        self.candidates.clear();
        let mut binary_clauses = HashMap::default();

        // Wall-clock guard (#8078): abort XOR detection on very large clause
        // databases to prevent preprocessing hangs.
        let find_start = std::time::Instant::now();
        const XOR_FIND_TIME_BUDGET_MS: u128 = 3000;

        // Process each clause
        for (idx, clause) in clauses.iter().enumerate() {
            // Wall-clock check every 8192 clauses to limit overhead.
            if idx & 0x1FFF == 0
                && idx > 0
                && find_start.elapsed().as_millis() >= XOR_FIND_TIME_BUDGET_MS
            {
                break;
            }
            self.process_clause_with_index(clause, idx);
            Self::record_binary_clause(&mut binary_clauses, clause);
        }

        let (xors, _) = self.collect_xors(&binary_clauses);
        xors
    }

    /// Find XORs and return which clause indices are consumed.
    ///
    /// This is useful for removing the CNF clauses that encode XORs
    /// after detection.
    pub fn find_xors_with_indices(
        &mut self,
        clauses: &[Vec<Literal>],
    ) -> (Vec<XorConstraint>, HashSet<usize>) {
        self.candidates.clear();
        let mut binary_clauses = HashMap::default();

        // Wall-clock guard (#8078): abort XOR detection on very large clause
        // databases to prevent preprocessing hangs.
        let find_start = std::time::Instant::now();
        const XOR_FIND_TIME_BUDGET_MS: u128 = 3000;

        // Process each clause with its index
        for (idx, clause) in clauses.iter().enumerate() {
            // Wall-clock check every 8192 clauses to limit overhead.
            if idx & 0x1FFF == 0
                && idx > 0
                && find_start.elapsed().as_millis() >= XOR_FIND_TIME_BUDGET_MS
            {
                break;
            }
            self.process_clause_with_index(clause, idx);
            Self::record_binary_clause(&mut binary_clauses, clause);
        }

        self.collect_xors(&binary_clauses)
    }

    /// Find complete XOR encodings and return each constraint with its exact
    /// CNF clause premises.
    ///
    /// This intentionally excludes the partial ternary-XOR + binary-support
    /// recovery path. The GF(2) certificate exporter needs a self-contained
    /// premise list for the CNF-to-linear-equation step; partial recovery is
    /// still used by the solver, but is not claimed as a complete algebraic
    /// certificate premise yet.
    pub(crate) fn find_complete_xors_with_clause_indices(
        &mut self,
        clauses: &[Vec<Literal>],
    ) -> Vec<XorDetection> {
        self.candidates.clear();

        let find_start = std::time::Instant::now();
        const XOR_FIND_TIME_BUDGET_MS: u128 = 3000;

        for (idx, clause) in clauses.iter().enumerate() {
            if idx & 0x1FFF == 0
                && idx > 0
                && find_start.elapsed().as_millis() >= XOR_FIND_TIME_BUDGET_MS
            {
                break;
            }
            self.process_clause_with_index(clause, idx);
        }

        let mut detections: Vec<XorDetection> = self
            .candidates
            .values()
            .filter(|candidate| candidate.is_complete())
            .map(|candidate| {
                let mut clause_indices = candidate.clause_indices.clone();
                clause_indices.sort_unstable();
                clause_indices.dedup();
                XorDetection {
                    constraint: candidate.to_constraint(),
                    clause_indices,
                }
            })
            .collect();
        detections.sort_by(|a, b| {
            a.constraint
                .vars
                .cmp(&b.constraint.vars)
                .then(a.constraint.rhs.cmp(&b.constraint.rhs))
        });
        detections
    }

    fn collect_xors(
        &self,
        binary_clauses: &HashMap<(VarId, VarId), Vec<BinaryClauseSupport>>,
    ) -> (Vec<XorConstraint>, HashSet<usize>) {
        let mut xors = Vec::new();
        let mut used_indices = HashSet::default();

        // Sort by variable list for deterministic iteration order
        let mut sorted_candidates: Vec<_> = self
            .candidates
            .values()
            .filter(|candidate| {
                candidate.is_complete() || candidate.is_supported_partial_xor(binary_clauses)
            })
            .collect();
        sorted_candidates.sort_by(|a, b| a.vars.cmp(&b.vars));

        for candidate in sorted_candidates {
            xors.push(candidate.to_constraint());
            for &idx in &candidate.clause_indices {
                used_indices.insert(idx);
            }
        }

        (xors, used_indices)
    }

    fn record_binary_clause(
        binary_clauses: &mut HashMap<(VarId, VarId), Vec<BinaryClauseSupport>>,
        clause: &[Literal],
    ) {
        if clause.len() != 2 {
            return;
        }

        let mut sorted_clause: Vec<Literal> = clause.to_vec();
        sorted_clause.sort_by_key(|lit| lit.variable().id());

        let lhs = sorted_clause[0].variable().id();
        let rhs = sorted_clause[1].variable().id();
        if lhs == rhs {
            return;
        }

        let forbidden_assignment = u8::from(!sorted_clause[0].is_positive())
            | (u8::from(!sorted_clause[1].is_positive()) << 1);

        binary_clauses
            .entry((lhs, rhs))
            .or_default()
            .push(BinaryClauseSupport {
                forbidden_assignment,
            });
    }

    /// Process a clause with its index for tracking which clauses form XORs.
    fn process_clause_with_index(&mut self, clause: &[Literal], idx: usize) {
        if clause.len() < MIN_XOR_SIZE || clause.len() > MAX_XOR_SIZE {
            return;
        }

        let mut sorted_clause: Vec<Literal> = clause.to_vec();
        sorted_clause.sort_by_key(|lit| lit.variable().id());

        let var_key: Vec<VarId> = sorted_clause
            .iter()
            .map(|lit| lit.variable().id())
            .collect();

        let var_set: HashSet<VarId> = var_key.iter().copied().collect();
        if var_set.len() != var_key.len() {
            return;
        }

        if let Some(candidate) = self.candidates.get_mut(&var_key) {
            if candidate.try_add(&sorted_clause) {
                candidate.clause_indices.push(idx);
            }
        } else if let Some(mut new_candidate) = PossibleXor::new(&sorted_clause) {
            new_candidate.clause_indices.push(idx);
            self.candidates.insert(var_key, new_candidate);
        }
    }
}
