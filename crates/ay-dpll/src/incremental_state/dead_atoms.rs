// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dead theory atoms on the session-persistent incremental lanes (#inc-dead-atoms).
//!
//! The persistent Tseitin maps keep every atom encoded during the session,
//! including atoms whose only assertions have since been popped. Handing those
//! atoms to the theory anyway made every `check-sat` pay for the whole session
//! history (registration, phase seeding, `suggest_decision` scans, and
//! disequality splits on dead `=` atoms whose fresh split vars then outlive the
//! check-sat).
//!
//! **Liveness is read off the ENCODING, not the assertion syntax.** An active
//! assertion `A` was encoded as the Tseitin cone of its ITE-lifted form; that
//! cone's root var is `encoded_assertions[A]` and every var in the cone maps
//! (through `var_to_term`) to a subterm of the lifted form — Tseitin mints no
//! terms of its own. So the live atoms of a check-sat are exactly the theory
//! atoms reachable from the root TERMS of the active assertions' roots
//! ([`encoded_live_atoms`]), which includes the ITE-lifted comparisons that
//! appear nowhere in the assertions as written. A term the encoding ALIASED
//! onto another term's var (`term_to_var[t]` owned by `var_to_term[v] != t`)
//! stands for that owner in the SAT cone and the theory receives the owner,
//! so the walk continues into the owner too. An atom is dead only if no
//! active root's cone reaches it; if any active assertion has no recorded
//! root the filter is off for that check-sat (every atom is handed over, the
//! pre-#inc-dead-atoms behaviour).
//!
//! **Soundness.** A withheld atom's SAT var stays in the clause DB, so the SAT
//! side still sees every clause; the theory simply receives fewer literals.
//! That can only weaken what the theory derives, PROVIDED every theory lemma is
//! T-valid for whatever subset of literals it was given. That proviso is the
//! theory's own soundness, not something this filter can supply: the first
//! version of this module withheld live ITE-lifted atoms, which merely steered
//! the search into a pre-existing LRA bug (`is_expression_forced_to_value`
//! ignored the sign of a negative row ratio and "pinned" `y - z` from the
//! one-sided `y - z <= 0`, `z - y >= 0`, refuting a satisfiable `y != z`); that
//! bug also produced a false UNSAT on the unfiltered base binary and is fixed
//! at its root in `ay-lra`. Completeness: a SAT model is re-validated against
//! the original assertions, and a missing revival or a non-converging split
//! loop fails closed (rejected model / Unknown → the from-scratch lane).

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermId, TermStore};

/// Split-loop round from which every remaining dead atom is revived.
///
/// Dead atoms that the split machinery maps onto an existing SAT var are
/// revived precisely (see `IncrementalNegationCache::take_reused_atoms`); this
/// bound is the convergence backstop for any reuse that path cannot observe
/// (e.g. a composite atom whose Tseitin delta re-uses a dead sub-atom). From
/// this round on the theory atom set is the pre-#inc-dead-atoms one.
pub(crate) const DEAD_ATOM_REVIVE_ALL_ITERATION: usize = 32;

/// Session counters for the dead-atom filter (cumulative across check-sats).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct DeadAtomStats {
    /// Dead atoms withheld from the theory at the start of a split loop.
    pub(crate) withheld: u64,
    /// Dead atoms handed back because the split machinery re-used their var.
    pub(crate) revived: u64,
    /// Split loops that hit [`DEAD_ATOM_REVIVE_ALL_ITERATION`] with atoms
    /// still withheld.
    pub(crate) revive_all: u64,
    /// Check-sats the engine arm left undecided to the from-scratch lane —
    /// the fail-closed path an unrevived dead atom would silently fall into.
    pub(crate) engine_fallbacks: u64,
}

/// The theory atoms in the encoded cone of the active assertions, or `None`
/// when some active assertion has no recorded encoding root (filter off).
///
/// `encoded_roots` maps each encoded assertion to its Tseitin root literal
/// (DIMACS, 1-indexed); `var_to_term`/`term_to_var` are the 0-indexed SAT-var
/// maps. The root var's term is the ITE-lifted assertion (or a sub-formula
/// Tseitin encoded it as), so the reachable theory atoms are precisely the
/// atoms whose vars that root depends on — including lifted comparisons absent
/// from the source text. When a reached term's var is OWNED by another term
/// (an alias: the theory is handed `var_to_term[var]`, not the term itself),
/// the owner and its subterms are reached as well.
pub(crate) fn encoded_live_atoms(
    terms: &TermStore,
    assertions: &[TermId],
    encoded_roots: &HashMap<TermId, i32>,
    var_to_term: &HashMap<u32, TermId>,
    term_to_var: &HashMap<TermId, u32>,
) -> Option<HashSet<TermId>> {
    let mut stack = Vec::with_capacity(assertions.len());
    for assertion in assertions {
        let root_lit = *encoded_roots.get(assertion)?;
        let root_var = root_lit.unsigned_abs().checked_sub(1)?;
        stack.push(*var_to_term.get(&root_var)?);
    }
    let mut seen: HashSet<TermId> = stack.iter().copied().collect();
    let mut live = HashSet::default();
    while let Some(term) = stack.pop() {
        if crate::is_theory_atom(terms, term) {
            live.insert(term);
        }
        let owner = term_to_var
            .get(&term)
            .and_then(|var| var_to_term.get(var))
            .copied();
        for next in terms.children(term).into_iter().chain(owner) {
            if seen.insert(next) {
                stack.push(next);
            }
        }
    }
    Some(live)
}

/// The theory atoms among `encoded_terms` outside the `live` set.
///
/// `live` is the encoded cone of the active assertions ([`encoded_live_atoms`]);
/// every other encoded term that is a theory atom is dead for this check-sat.
pub(crate) fn dead_theory_atoms(
    terms: &TermStore,
    encoded_terms: impl IntoIterator<Item = TermId>,
    live: &HashSet<TermId>,
) -> HashSet<TermId> {
    encoded_terms
        .into_iter()
        .filter(|term| !live.contains(term) && crate::is_theory_atom(terms, *term))
        .collect()
}

/// Append the live theory atoms of `var_to_term` that are not yet in `atoms`,
/// in ascending SAT-var order, keeping `atoms`/`atom_set` append-only.
///
/// An atom is live when it is active or a theory atom, and not in `dead`.
/// Existing entries never move, so a consumer that registers only the tail
/// added since its last visit (the cached extension path) sees every newly
/// live atom exactly once — including a revived dead atom with an old var id.
pub(crate) fn append_live_theory_atoms(
    terms: &TermStore,
    var_to_term: &HashMap<u32, TermId>,
    active_atoms: &HashSet<TermId>,
    dead: &HashSet<TermId>,
    atoms: &mut Vec<TermId>,
    atom_set: &mut HashSet<TermId>,
) {
    for (_, term) in crate::iter_var_to_term_sorted(var_to_term) {
        if dead.contains(&term) || atom_set.contains(&term) {
            continue;
        }
        if active_atoms.contains(&term) || crate::is_theory_atom(terms, term) {
            atom_set.insert(term);
            atoms.push(term);
        }
    }
}

/// The per-check-sat dead-atom filter of the session-persistent split loop.
///
/// Built once per check-sat from the atoms encoded so far; it is off on every
/// lane whose atom maps are rebuilt per check-sat (no dead atoms).
pub(crate) struct DeadAtomFilter {
    dead: HashSet<TermId>,
    on: bool,
}

impl DeadAtomFilter {
    /// `live` is [`encoded_live_atoms`] (plus the syntactically active
    /// atoms); `None` disables the filter for this check-sat.
    pub(crate) fn new(
        terms: &TermStore,
        encoded_terms: impl IntoIterator<Item = TermId>,
        live: Option<&HashSet<TermId>>,
    ) -> Self {
        let dead = match live {
            Some(live) => dead_theory_atoms(terms, encoded_terms, live),
            None => HashSet::default(),
        };
        let on = !dead.is_empty();
        Self { dead, on }
    }

    /// The filter for one check-sat of a session-persistent split loop:
    /// live = the encoded cone of the active `assertions` plus the
    /// syntactically active atoms `base_active` (Bool UF args and the like),
    /// each followed to the owner of its SAT var when the encoding aliased it.
    /// Off when `enabled` is false or an active assertion has no encoding root.
    pub(crate) fn for_check_sat(
        enabled: bool,
        terms: &TermStore,
        assertions: &[TermId],
        encoded_roots: &HashMap<TermId, i32>,
        var_to_term: &HashMap<u32, TermId>,
        term_to_var: &HashMap<TermId, u32>,
        base_active: &HashSet<TermId>,
    ) -> Self {
        let live = enabled
            .then(|| encoded_live_atoms(terms, assertions, encoded_roots, var_to_term, term_to_var))
            .flatten()
            .map(|mut live| {
                // A syntactically active atom aliased onto another term's var
                // is handed to the theory as that owner: keep both live.
                let owner = |t: &TermId| term_to_var.get(t).and_then(|v| var_to_term.get(v));
                let owners: Vec<TermId> = base_active.iter().filter_map(owner).copied().collect();
                live.extend(base_active.iter().copied().chain(owners));
                live
            });
        Self::new(terms, var_to_term.values().copied(), live.as_ref())
    }

    /// Whether this check-sat withholds (or withheld) any atom.
    pub(crate) fn is_on(&self) -> bool {
        self.on
    }

    /// Atoms currently withheld from the theory.
    pub(crate) fn withheld(&self) -> usize {
        self.dead.len()
    }

    /// Whether `term` is withheld: it has a SAT var but the theory never sees it.
    pub(crate) fn is_dead(&self, term: &TermId) -> bool {
        self.dead.contains(term)
    }

    /// Before split-loop round `iteration`: revive the `reused` atoms the
    /// previous round's encoding mapped onto their existing vars, or — the
    /// convergence backstop — every atom from
    /// [`DEAD_ATOM_REVIVE_ALL_ITERATION`] on. Returns whether any atom revived.
    pub(crate) fn revive(
        &mut self,
        iteration: usize,
        reused: Vec<TermId>,
        stats: &mut DeadAtomStats,
    ) -> bool {
        let before = self.dead.len();
        if iteration >= DEAD_ATOM_REVIVE_ALL_ITERATION {
            if before > 0 {
                stats.revive_all += 1;
            }
            self.dead.clear();
        } else {
            for term in reused {
                if self.dead.remove(&term) {
                    stats.revived += 1;
                }
            }
        }
        let revived = self.dead.len() < before;
        if revived {
            tracing::debug!(
                iteration,
                still_dead = self.dead.len(),
                "#inc-dead-atoms revived"
            );
        }
        revived
    }

    /// [`append_live_theory_atoms`] with this filter's dead set.
    pub(crate) fn append_live(
        &self,
        terms: &TermStore,
        var_to_term: &HashMap<u32, TermId>,
        active_atoms: &HashSet<TermId>,
        atoms: &mut Vec<TermId>,
        atom_set: &mut HashSet<TermId>,
    ) {
        append_live_theory_atoms(
            terms,
            var_to_term,
            active_atoms,
            &self.dead,
            atoms,
            atom_set,
        );
    }
}

#[cfg(test)]
#[path = "dead_atoms_tests.rs"]
mod tests;
