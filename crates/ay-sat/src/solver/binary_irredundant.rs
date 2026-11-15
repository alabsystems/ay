// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kissat 4.0.4's irredundant binaries (`--sat-binary-irredundant-kissat`).
//!
//! Kissat has no redundant binary clauses: every size-2 clause goes through
//! `new_binary_clause` and counts as irredundant (clause.c:64-79, 109-117;
//! watch.h has no redundant bit). A learned binary, one strengthened by OTFS,
//! one vivified or one shrunk at level 0 therefore counts in elimination
//! scores and bounds, is resolved on, feeds factoring and the BINIRR scale,
//! and is never reduced. AY keeps learned binaries learned: BVE's occurrence
//! lists skip them, elimination deletes those holding an eliminated variable,
//! factor ignores them and reduction may delete them.
//!
//! Under the switch every live learned binary is promoted to irredundant at
//! the start of each reduction and of each simplification round, which is
//! where their status is read. Hyper-binary resolvents keep their one-round
//! lifetime (they have no Kissat counterpart). Promotion changes only the
//! clause's status, not the proof: the clause stays a derived constraint, and
//! VeriPB's checked deletion of a formula clause at worst downgrades to an
//! unchecked one, which a refutation tolerates (`proof/veripb.rs`). Off under
//! LRAT and in incremental or scoped solving, where a learned clause may
//! depend on clauses that are later removed.

use super::*;

impl Solver {
    /// Promote every live learned binary (hyper resolvents excepted) to
    /// irredundant under `--sat-binary-irredundant-kissat`.
    pub(super) fn promote_learned_binaries_kissat(&mut self) {
        if !self.cold.binary_irredundant_kissat
            || self.cold.lrat_enabled
            || self.cold.has_been_incremental
            || self.in_scoped_mode()
        {
            return;
        }
        let binaries: Vec<usize> = self
            .arena
            .learned_indices()
            .filter(|&idx| {
                self.arena.len_of(idx) == 2
                    && !self.arena.is_hyper(idx)
                    && !self.arena.is_garbage_any(idx)
            })
            .collect();
        for idx in binaries {
            self.arena.set_learned(idx, false);
            let lits: Vec<Literal> = self.arena.literals(idx).to_vec();
            self.note_clause_promoted_to_irredundant(idx, &lits);
        }
    }
}
