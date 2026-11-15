// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What one ground solve of a query hands to the next.
//!
//! A quantified query solves its ground problem many times: once per
//! E-matching batch, once per datatype unrolling depth, once per unknown
//! retry. Each solve runs in its own incremental state
//! (`with_isolated_incremental_state`), with a new SAT solver and a new
//! Tseitin encoding. The lazy split loop reaches a theory-consistent
//! assignment by learning one theory conflict per round, as clauses scoped to
//! that solver, so the next solve, whose assertions differ by a handful of
//! instances, walks the whole way again: on the queries this was measured on,
//! as many rounds for a re-solve that adds three atoms as for the first solve.
//!
//! This store keeps, outside any SAT solver and keyed by term:
//!
//! * the theory conflicts the earlier solves derived, and
//! * the SAT assignment the last solve ended on.
//!
//! The next lazy split loop adds the conflicts as clauses and takes the
//! assignment as decision phases before its first round, so its first model is
//! the last solve's model wherever the new assertions allow it, and its rounds
//! go to what the new assertions changed. The two only work together: phases
//! without the conflicts start from the old model and leave it at the first
//! theory hint; conflicts without the phases start from another assignment and
//! meet other conflicts.
//!
//! # Soundness: why a carried clause holds in every later re-solve
//!
//! Phases are a preference, nothing more: a SAT solver seeded with any phases
//! decides the same formula.
//!
//! A conflict clause is a constraint. A clause the search learned is only
//! known to follow from THAT search's context: the conflict gate
//! (`verify_conflict_semantic_memoized`) re-derives a conflict together with
//! the query's support literals (ground instances of asserted quantifiers,
//! datatype facts), samples its EUF re-check, and lets through what it cannot
//! decide. The theory that derived the conflict also saw facts its
//! explanation need not name (top-level disequalities of the assertions).
//! Such a clause is a consequence of one assertion set, one push/pop scope,
//! one ground instantiation; it is not safe in a solve over another (a nested
//! probe of a subset, a retry over a rewritten window, a solve after the
//! instances changed). So a conflict enters this store only when its literal
//! set is inconsistent in the theory BY ITSELF, which this store checks for
//! itself and takes from no caller:
//!
//! * a Farkas certificate the conflict carries passes the semantic check
//!   against the literals (`verify_theory_conflict_with_farkas_full`), or
//! * a fresh theory solver given the literals and nothing else (no support
//!   literal, no assertion, no sampling) derives a contradiction
//!   ([`crate::verification::conflict_is_refuted_on_its_own`]).
//!
//! Neither check reads an assertion, a scope or an instance. What a `true`
//! depends on is the term store alone: the structure behind each `TermId` and
//! the interpretation the theory gives each symbol. Every free symbol (a
//! declared constant, a Skolem, a purification variable, an instance's
//! ground term) is read as unconstrained, so the literal set is unsatisfiable
//! for EVERY value of every free symbol, and the clause that negates it holds
//! in every model of the theory, whatever is asserted. Adding it to the
//! encoding of ANY later ground solve over the same terms therefore removes
//! only assignments no theory model has: a satisfiable problem keeps every
//! model, an unsatisfiable one was that already. No scope, assertion set or
//! instantiation is assumed, so none can change under it.
//!
//! What remains is that the terms keep their meaning while the clause is
//! held, which the store enforces, and how long it is held:
//!
//! * A stored literal is a `TermId`. The id names the same term only while
//!   the term store has grown by appending: a speculative rollback, a
//!   compaction or a replaced (cloned) store reuses or renames ids. The store
//!   keeps the snapshot stamp of the term store it read from and empties
//!   itself as soon as that stamp is no longer an append-only prefix of the
//!   store it is asked about.
//! * The builtin `to_real` and `is_int` change meaning when a user declares a
//!   function of that name (the store's shadow latches). The store records
//!   both latches and empties itself when either moves.
//! * Declarations happen between commands, so a store that serves one public
//!   query never sees one: `begin_public_solve` empties it. Nothing is carried
//!   from one `check-sat` to the next, in particular nothing across a
//!   `push`/`pop`.
//!
//! Policy, not soundness: no conflict is offered or replayed by a solve that
//! records a proof (its clause ledger records where every clause came from),
//! nor by a re-solve used as evidence (a checking solve or a certification
//! re-solve, see `strengthening.rs`), which searches exactly as it did before
//! this store existed. See [`Executor::ground_solve_carry_active`].
//!
//! # Which atoms a replayed conflict may bring along
//!
//! A conflict often mentions atoms its loop minted itself: the two sides of an
//! expression split, a model equality. The next encoding has not minted them
//! yet, and a conflict that waits for them is not there when the same split
//! is requested again. Each literal therefore records whether its atom was
//! minted by the loop. A conflict is replayed when every atom that came from
//! the ASSERTIONS has a SAT variable in the new encoding; its minted atoms are
//! encoded on the way in, exactly as a theory lemma's atoms are. A conflict
//! over an assertion atom the new problem does not have is left out, and a
//! conflict with no assertion atom at all is not kept. Both are choices about
//! usefulness: the clause would be valid in either case.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermStoreSnapshotStamp;
use ay_core::{TermId, TermStore, TheoryConflict, TheoryLit};
use ay_sat::{Solver as SatSolver, Variable as SatVariable};

use super::Executor;

/// Literals the store may hold in total. A carried conflict has three or four
/// literals in practice, so this is room for a few hundred thousand of them;
/// past it nothing more is recorded and the solves fall back to deriving.
const MAX_CARRIED_LITERALS: usize = 1 << 20;

/// Literal sets remembered as NOT carriable, so the fresh-solver check is not
/// repeated for a conflict every solve derives again.
const MAX_DECLINED_SETS: usize = 1 << 16;

/// A theory conflict a lazy split loop has just derived, as the theory
/// reported it.
#[derive(Clone, Copy, Debug)]
pub(crate) enum OfferedConflict<'a> {
    /// A bare literal set.
    Literals(&'a [TheoryLit]),
    /// A literal set with the theory's Farkas annotation, if it made one.
    Farkas(&'a TheoryConflict),
}

impl OfferedConflict<'_> {
    fn literals(&self) -> &[TheoryLit] {
        match self {
            Self::Literals(literals) => literals,
            Self::Farkas(conflict) => &conflict.literals,
        }
    }

    /// Whether the literal set is inconsistent in the theory by itself (see
    /// the module docs). A Farkas certificate that passes the semantic check
    /// settles it; otherwise, or when it fails, a fresh solver decides.
    fn is_refuted_on_its_own(&self, key: &[TheoryLit], terms: &TermStore) -> bool {
        if let Self::Farkas(conflict) = self {
            if conflict.farkas.is_some()
                && crate::verification::verify_theory_conflict_with_farkas_full(conflict, terms)
                    .is_ok()
            {
                return true;
            }
        }
        crate::verification::conflict_is_refuted_on_its_own(key, terms)
    }
}

/// One literal of a carried conflict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CarriedLiteral {
    pub(crate) literal: TheoryLit,
    /// The loop that derived the conflict minted this atom itself (a split
    /// side, a model equality): the replaying loop may encode it. `false` for
    /// an atom of the assertions, which the replaying encoding must have.
    pub(crate) minted: bool,
}

/// The term store an entry was read from: its snapshot stamp and the two
/// latches that change what an existing term means.
#[derive(Clone, Debug)]
struct TermsRead {
    stamp: TermStoreSnapshotStamp,
    to_real_shadowed: bool,
    is_int_shadowed: bool,
}

impl TermsRead {
    fn of(terms: &TermStore) -> Self {
        Self {
            stamp: terms.snapshot_stamp(),
            to_real_shadowed: terms.to_real_is_shadowed(),
            is_int_shadowed: terms.is_int_is_shadowed(),
        }
    }

    /// Every id below the recorded length still names the same term, with
    /// the same meaning, in `terms`.
    fn still_describes(&self, terms: &TermStore) -> bool {
        self.stamp.is_append_only_prefix_of(terms)
            && self.to_real_shadowed == terms.to_real_is_shadowed()
            && self.is_int_shadowed == terms.is_int_is_shadowed()
    }
}

/// What the ground solves of one public query hand to each other.
#[derive(Default)]
pub(crate) struct GroundSolveCarry {
    /// Each entry is sorted by literal and free of duplicates; its literals
    /// are jointly inconsistent in the theory.
    conflicts: Vec<Vec<CarriedLiteral>>,
    known: HashSet<Vec<TheoryLit>>,
    /// Literal sets the standalone check did not refute.
    declined: HashSet<Vec<TheoryLit>>,
    literals: usize,
    /// The truth value each term had in the SAT assignment the last ground
    /// solve ended on.
    phases: HashMap<TermId, bool>,
    /// The term store every stored `TermId` was read from.
    terms_read: Option<TermsRead>,
    recorded: u64,
    replayed: u64,
}

impl GroundSolveCarry {
    /// Forget everything: a new public query starts.
    pub(crate) fn begin_query(&mut self) {
        self.clear();
        self.recorded = 0;
        self.replayed = 0;
    }

    fn clear(&mut self) {
        self.conflicts.clear();
        self.known.clear();
        self.declined.clear();
        self.literals = 0;
        self.phases.clear();
        self.terms_read = None;
    }

    /// Conflicts recorded and conflict clauses replayed in this query.
    pub(crate) fn counters(&self) -> (u64, u64) {
        (self.recorded, self.replayed)
    }

    #[cfg(test)]
    pub(crate) fn conflict_count(&self) -> usize {
        self.conflicts.len()
    }

    /// Empty the store unless `terms` is the store the entries were read from,
    /// grown only by appending, with the same shadow latches.
    fn retire_unless_same_terms(&mut self, terms: &TermStore) {
        let same = self
            .terms_read
            .as_ref()
            .is_none_or(|read| read.still_describes(terms));
        if !same {
            self.clear();
        }
    }

    /// Offer a conflict a lazy split loop has just derived. It is stored when
    /// this store's own check shows its literal set inconsistent in the
    /// theory alone (see the module docs). `minted` says which atoms the loop
    /// minted itself. Returns whether the conflict was stored.
    pub(crate) fn offer(
        &mut self,
        terms: &TermStore,
        conflict: OfferedConflict<'_>,
        minted: &dyn Fn(TermId) -> bool,
    ) -> bool {
        self.retire_unless_same_terms(terms);
        let mut key = conflict.literals().to_vec();
        key.sort_unstable();
        key.dedup();
        if key.is_empty()
            || self.known.contains(&key)
            || self.declined.contains(&key)
            || self.literals.saturating_add(key.len()) > MAX_CARRIED_LITERALS
        {
            return false;
        }
        // One atom asserted both ways negates to a tautology.
        if key.windows(2).any(|pair| pair[0].term == pair[1].term) {
            return false;
        }
        // A conflict among minted atoms only says nothing about the
        // assertions; no later solve could tell whether it concerns it.
        if key.iter().all(|literal| minted(literal.term)) {
            return false;
        }
        let standalone = conflict.is_refuted_on_its_own(&key, terms);
        // Every id in `key` is below the store's current length, so what is
        // read now covers this entry and every earlier one.
        self.terms_read = Some(TermsRead::of(terms));
        if !standalone {
            if self.declined.len() < MAX_DECLINED_SETS {
                self.declined.insert(key);
            }
            return false;
        }
        self.literals += key.len();
        self.conflicts.push(
            key.iter()
                .map(|&literal| CarriedLiteral {
                    literal,
                    minted: minted(literal.term),
                })
                .collect(),
        );
        self.known.insert(key);
        self.recorded += 1;
        true
    }

    /// The stored conflicts, for a lazy split loop over `terms` to replay.
    pub(crate) fn conflicts(&mut self, terms: &TermStore) -> &[Vec<CarriedLiteral>] {
        self.retire_unless_same_terms(terms);
        &self.conflicts
    }

    pub(crate) fn note_replayed(&mut self, clauses: usize) {
        self.replayed += clauses as u64;
    }

    /// Remember the SAT assignment a ground solve ended on, term by term.
    pub(crate) fn remember_assignment(
        &mut self,
        terms: &TermStore,
        var_to_term: &HashMap<u32, TermId>,
        assignment: &[bool],
    ) {
        self.retire_unless_same_terms(terms);
        for (&var, &term) in var_to_term {
            if let Some(&value) = assignment.get(var as usize) {
                self.phases.insert(term, value);
            }
        }
        self.terms_read = Some(TermsRead::of(terms));
    }

    /// Make the remembered value of every term this encoding has the
    /// preferred polarity of its SAT variable. Returns the variables seeded.
    pub(crate) fn seed_phases(
        &mut self,
        terms: &TermStore,
        solver: &mut SatSolver,
        term_to_var: &HashMap<TermId, u32>,
    ) -> usize {
        self.retire_unless_same_terms(terms);
        if self.phases.is_empty() {
            return 0;
        }
        let mut seeded = 0usize;
        for (term, &var) in term_to_var {
            if let Some(&value) = self.phases.get(term) {
                solver.set_var_phase(SatVariable::new(var), value);
                seeded += 1;
            }
        }
        seeded
    }
}

impl Executor {
    /// Whether this executor's lazy split loops hand conflicts and phases to
    /// each other. Off in a proof-tracked solve (`proof_enabled`), outside the
    /// quantifier pipeline (one ground solve per query), and in every re-solve
    /// used as evidence: a checking solve, a nested probe of one, or a
    /// certification re-solve of a derived query. Those search exactly as they
    /// did before the store existed.
    pub(in crate::executor) fn ground_solve_carry_active(&self, proof_enabled: bool) -> bool {
        !proof_enabled
            && self.quantifier_pipeline_engaged
            && !self.certification_resolve
            && !self.in_evidence_solve()
    }
}

#[cfg(test)]
#[path = "ground_solve_carry_tests.rs"]
mod tests;
