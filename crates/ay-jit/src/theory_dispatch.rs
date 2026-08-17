// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JIT-compiled theory atom dispatch table (#8177).
//!
//! Replaces HashMap-based `var_to_term` lookups in the DPLL(T) theory
//! extension's `propagate()` hot loop with an O(1) array-indexed dispatch
//! table. The original code does:
//!
//! ```text
//! if self.is_theory_atom(var) {
//!     if let Some(&term) = self.var_to_term.get(&var.id()) {
//!         // ... ITE guard bitset check ...
//!         self.theory.assert_literal(term, value);
//!     }
//! }
//! ```
//!
//! This involves a HashSet membership test + HashMap lookup (~10-30ns per
//! atom on cache miss). The dispatch table replaces both with a single
//! array index: `dispatch_table[var_id]` which returns the term ID and
//! ITE guard information in one cache-friendly access.
//!
//! ## Architecture
//!
//! The table is a flat `Vec<Option<TheoryAtomEntry>>` indexed by SAT
//! variable ID. For a typical QF_LIA formula with 50K SAT variables and
//! 5K theory atoms, this costs ~400KB (8 bytes per entry × 50K) but
//! eliminates all hash overhead on the hot path.

/// Entry for a single theory atom in the dispatch table.
///
/// Packed to minimize cache footprint: 12 bytes per entry (vs 64+ bytes
/// for a HashMap bucket chain).
#[derive(Debug, Clone, Copy)]
pub struct TheoryAtomEntry {
    /// The term ID in the theory solver's term store.
    pub term_id: u32,
    /// SAT variable ID of the ITE condition guard, or `u32::MAX` if
    /// this atom is not ITE-guarded.
    pub ite_cond_var: u32,
    /// Whether this atom is in the "then" branch of the ITE.
    /// Only meaningful when `ite_cond_var != u32::MAX`.
    pub is_then_branch: bool,
}

impl TheoryAtomEntry {
    /// Whether this atom is guarded by an ITE condition.
    #[inline(always)]
    pub fn is_ite_guarded(&self) -> bool {
        self.ite_cond_var != u32::MAX
    }
}

/// Result of dispatching a literal assignment through the theory table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TheoryDispatchResult {
    /// The atom should be asserted to the theory solver.
    Assert {
        /// Term ID to assert.
        term_id: u32,
        /// Truth value of the assertion.
        value: bool,
    },
    /// The atom is in an inactive ITE branch; defer until final check.
    DeferIte {
        /// Term ID that was deferred.
        term_id: u32,
        /// Truth value that was deferred.
        value: bool,
    },
    /// The variable is not a theory atom; skip.
    Skip,
}

/// Theory family known to the external code generation CDCL loop specializer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TheoryInlineKind {
    /// Linear real arithmetic.
    Lra,
    /// Linear integer arithmetic.
    Lia,
    /// Bit-vector theory.
    Bv,
    /// Equality with uninterpreted functions.
    Euf,
    /// CHC/PDR helper expression region.
    Chc,
    /// Caller-provided theory family that has not been classified yet.
    Other,
}

/// One theory participant visible to the CDCL loop specializer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TheoryInlineParticipant {
    /// Theory family.
    pub kind: TheoryInlineKind,
    /// Whether the current formula shape can call this theory directly from
    /// propagation rather than through the generic callback/vtable path.
    pub direct_propagate_available: bool,
    /// Whether the generic `can_propagate()` check is known true at compile
    /// time and can be baked into the generated loop.
    pub can_propagate_known_true: bool,
}

impl TheoryInlineParticipant {
    /// Participant whose propagation call can be emitted directly.
    #[must_use]
    pub fn direct(kind: TheoryInlineKind) -> Self {
        Self {
            kind,
            direct_propagate_available: true,
            can_propagate_known_true: true,
        }
    }

    /// Participant that must remain on the generic callback path.
    #[must_use]
    pub fn generic(kind: TheoryInlineKind) -> Self {
        Self {
            kind,
            direct_propagate_available: false,
            can_propagate_known_true: false,
        }
    }
}

/// Formula-level facts used before emitting a theory-inlined CDCL loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoryInlineProfile {
    /// Theory participants detected during formula analysis.
    pub participants: Vec<TheoryInlineParticipant>,
    /// Number of SAT variables that map to theory atoms.
    pub theory_atom_count: u32,
    /// Whether any theory atom has an ITE relevancy guard.
    pub has_ite_guards: bool,
}

impl TheoryInlineProfile {
    /// Pure SAT profile: the generated loop can erase theory callbacks.
    #[must_use]
    pub fn pure_sat() -> Self {
        Self {
            participants: Vec::new(),
            theory_atom_count: 0,
            has_ite_guards: false,
        }
    }

    /// Single-theory profile for formulas where one theory owns all theory
    /// atoms and has a direct propagation entry point.
    #[must_use]
    pub fn single_direct(kind: TheoryInlineKind, theory_atom_count: u32) -> Self {
        Self {
            participants: vec![TheoryInlineParticipant::direct(kind)],
            theory_atom_count,
            has_ite_guards: false,
        }
    }
}

/// Specialization mode selected for external code generation CDCL loop emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TheoryInlineMode {
    /// Pure SAT: theory callback state is compiled away.
    PureSat,
    /// One directly callable theory: inline one propagate/check path and omit
    /// the Nelson-Oppen fixpoint scheduler.
    SingleTheoryDirect(TheoryInlineKind),
    /// Multiple directly callable theories: direct calls are possible, but the
    /// Nelson-Oppen/fixpoint interleaving must stay in the generated loop.
    CombinedTheoryDirect,
    /// At least one participant still needs the generic callback path.
    GenericCallback,
}

/// Bounded planning result for theory-inlined CDCL loop generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TheoryInlinePlan {
    /// Selected loop shape.
    pub mode: TheoryInlineMode,
    /// Whether the generated loop should include any theory callback dispatch.
    pub uses_theory_callback: bool,
    /// Whether `can_propagate()` checks can be folded out of the hot loop.
    pub bakes_can_propagate: bool,
    /// Whether Nelson-Oppen/fixpoint interleaving is still required.
    pub requires_fixpoint_interleaving: bool,
    /// Whether ITE relevancy handling must remain in the atom-dispatch path.
    pub preserves_ite_relevancy: bool,
}

impl TheoryInlinePlan {
    /// Build the external code generation loop-emission plan from formula analysis facts.
    #[must_use]
    pub fn from_profile(profile: &TheoryInlineProfile) -> Self {
        let preserves_ite_relevancy = profile.has_ite_guards;
        if profile.participants.is_empty() || profile.theory_atom_count == 0 {
            return Self {
                mode: TheoryInlineMode::PureSat,
                uses_theory_callback: false,
                bakes_can_propagate: true,
                requires_fixpoint_interleaving: false,
                preserves_ite_relevancy,
            };
        }

        let all_direct = profile
            .participants
            .iter()
            .all(|participant| participant.direct_propagate_available);
        let all_can_propagate_known = profile
            .participants
            .iter()
            .all(|participant| participant.can_propagate_known_true);

        if !all_direct {
            return Self {
                mode: TheoryInlineMode::GenericCallback,
                uses_theory_callback: true,
                bakes_can_propagate: false,
                requires_fixpoint_interleaving: profile.participants.len() > 1,
                preserves_ite_relevancy,
            };
        }

        match profile.participants.as_slice() {
            [participant] => Self {
                mode: TheoryInlineMode::SingleTheoryDirect(participant.kind),
                uses_theory_callback: false,
                bakes_can_propagate: all_can_propagate_known,
                requires_fixpoint_interleaving: false,
                preserves_ite_relevancy,
            },
            _ => Self {
                mode: TheoryInlineMode::CombinedTheoryDirect,
                uses_theory_callback: false,
                bakes_can_propagate: all_can_propagate_known,
                requires_fixpoint_interleaving: true,
                preserves_ite_relevancy,
            },
        }
    }
}

/// Array-indexed theory atom dispatch table.
///
/// Provides O(1) lookup for theory atom information, replacing the
/// HashMap-based `var_to_term` and `theory_atom_set` in the theory
/// extension's `propagate()` hot loop.
pub struct TheoryDispatchTable {
    /// Per-variable entry. Indexed by SAT variable ID.
    /// `None` means the variable is not a theory atom.
    atoms: Vec<Option<TheoryAtomEntry>>,
    /// Number of theory atoms registered.
    compiled_count: u32,
}

impl TheoryDispatchTable {
    /// Create an empty dispatch table.
    pub fn new() -> Self {
        Self {
            atoms: Vec::new(),
            compiled_count: 0,
        }
    }

    /// Build the dispatch table from (var_id, term_id) pairs.
    ///
    /// # Arguments
    ///
    /// * `var_atoms` - Iterator of (SAT variable ID, theory term ID) pairs.
    /// * `ite_guards` - Slice of (var_id, cond_var_id, is_then_branch) for
    ///   ITE-guarded atoms. Only entries present here get ITE guard info.
    pub fn compile(
        &mut self,
        var_atoms: impl IntoIterator<Item = (u32, u32)>,
        ite_guards: &[(u32, u32, bool)],
    ) {
        // First pass: determine max var ID and collect entries.
        let entries: Vec<(u32, u32)> = var_atoms.into_iter().collect();
        let max_var = entries.iter().map(|(v, _)| *v).max().unwrap_or(0) as usize;

        self.atoms.clear();
        self.atoms.resize(max_var + 1, None);
        self.compiled_count = 0;

        for (var_id, term_id) in entries {
            let idx = var_id as usize;
            if idx < self.atoms.len() {
                self.atoms[idx] = Some(TheoryAtomEntry {
                    term_id,
                    ite_cond_var: u32::MAX,
                    is_then_branch: false,
                });
                self.compiled_count += 1;
            }
        }

        // Apply ITE guards.
        for &(var_id, cond_var, is_then_branch) in ite_guards {
            let idx = var_id as usize;
            if let Some(Some(ref mut entry)) = self.atoms.get_mut(idx) {
                entry.ite_cond_var = cond_var;
                entry.is_then_branch = is_then_branch;
            }
        }
    }

    /// Look up a theory atom entry by SAT variable ID. O(1).
    #[inline(always)]
    pub fn get(&self, var_id: u32) -> Option<&TheoryAtomEntry> {
        self.atoms.get(var_id as usize).and_then(|e| e.as_ref())
    }

    /// Check whether a SAT variable is a theory atom. O(1).
    #[inline(always)]
    pub fn is_theory_atom(&self, var_id: u32) -> bool {
        self.atoms.get(var_id as usize).is_some_and(Option::is_some)
    }

    /// Set or update ITE guard information for a variable.
    pub fn set_ite_guard(&mut self, var_id: u32, cond_var: u32, is_then_branch: bool) {
        let idx = var_id as usize;
        if let Some(Some(ref mut entry)) = self.atoms.get_mut(idx) {
            entry.ite_cond_var = cond_var;
            entry.is_then_branch = is_then_branch;
        }
    }

    /// Number of theory atoms in the table.
    pub fn len(&self) -> usize {
        self.compiled_count as usize
    }

    /// Whether the table is empty.
    pub fn is_empty(&self) -> bool {
        self.compiled_count == 0
    }

    /// Dispatch a literal assignment through the theory table.
    ///
    /// Replaces the hot-loop code in `TheoryExtension::propagate_impl()`:
    /// `is_theory_atom` check + `var_to_term` HashMap lookup + ITE guard
    /// bitset check, all in a single array access.
    ///
    /// # Arguments
    ///
    /// * `var_id` - SAT variable ID of the assigned literal.
    /// * `value` - Truth value of the assignment.
    /// * `cond_value` - Function to query the current assignment of an
    ///   ITE condition variable. Returns `Some(bool)` if assigned.
    /// * `decision_level` - Current SAT decision level (ITE deferral
    ///   only applies at level > 0).
    #[inline]
    pub fn dispatch_assignment(
        &self,
        var_id: u32,
        value: bool,
        cond_value: &impl Fn(u32) -> Option<bool>,
        decision_level: u32,
    ) -> TheoryDispatchResult {
        let idx = var_id as usize;
        let entry = match self.atoms.get(idx) {
            Some(Some(e)) => e,
            _ => return TheoryDispatchResult::Skip,
        };

        // ITE relevancy check (#8254, #8003): defer ITE-guarded atoms when
        // the condition IS assigned AND selects the other branch.
        //
        // When the condition is unassigned, assert normally -- CDCL
        // backtracking handles any conflicts from simultaneously-active
        // branches. The previous approach (defer when unassigned) was too
        // aggressive: it starved the theory solver on ITE-heavy benchmarks,
        // causing timeouts on satisfiable QF_LRA instances (sc-6, etc.).
        //
        // At level 0, ITE deferral is skipped entirely because level-0
        // assertions are permanent and cannot be backtracked. The non-JIT
        // path guards this with `sat_level > 0`.
        if entry.is_ite_guarded() && decision_level > 0 {
            if let Some(cond_val) = cond_value(entry.ite_cond_var) {
                if cond_val != entry.is_then_branch {
                    return TheoryDispatchResult::DeferIte {
                        term_id: entry.term_id,
                        value,
                    };
                }
            }
        }

        TheoryDispatchResult::Assert {
            term_id: entry.term_id,
            value,
        }
    }

    /// Total capacity of the table (max var ID + 1).
    pub fn capacity(&self) -> usize {
        self.atoms.len()
    }
}

impl Default for TheoryDispatchTable {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
#[path = "theory_dispatch/tests.rs"]
mod tests;
