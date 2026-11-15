// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The forged-UNSAT guard re-decides the authored problem over the terms it
//! names, not over the outer solve's scratch.
//!
//! Step (1) of the deferred-trust discharge (`redecides_definitive_sat_within`)
//! clones the outer executor's context into a derived executor and re-solves
//! the authored assertions under a 250 ms budget. The clone brings the whole
//! arena with it, including everything the search and proof planning
//! interned afterwards: nothing asserts that scaffolding, but whole-store
//! scans in the nested solve still walk it. Measured on the model-checker-consumer
//! `nested_query_false_unsat` row: the guard cloned 25,826 terms and its
//! re-solve returned `Unknown` after 313-1087 ms, at and past its own 250 ms
//! budget, on a refutation that is ground.
//!
//! Step (4)'s whole-problem re-solve has rebuilt its arena around the query
//! for the same reason since d9ccc7a45; this is the same rebuild, in the same
//! order (roots installed first). The compaction reclaims exactly the terms
//! the context can no longer NAME; surviving `TermData` is byte-identical and
//! only ids move, so the guard asks the same question over the same terms.
//!
//! This guard is downgrade-only, so abstaining is its PERMISSIVE direction and
//! the rebuild must never make it abstain where it used to run. The compaction
//! copies the surviving terms into a fresh arena beside the clone; when the
//! memory limit leaves no room for that copy, the guard re-decides over the
//! clone as it stands, exactly as it did before the rebuild existed. Only a
//! context the compaction could not relabel -- already rewritten in place, so
//! no longer the clone -- abandons the re-solve.

use super::{probe_cert_reject, Executor};
use crate::executor::quantifier_loop::result_mapping::compact_derived_arena;

impl Executor {
    /// Rebuild the guard's derived arena around the authored roots already
    /// installed as `exec.ctx.assertions`. `false` abandons the re-solve.
    pub(super) fn rebuild_forged_guard_arena(&self, exec: &mut Executor) -> bool {
        if !crate::memory::probe_clone_fits(exec.ctx.terms.true_memory_bytes(), self.memory_limit())
        {
            return true;
        }
        match compact_derived_arena(&mut exec.ctx) {
            // An arena whose internal names spell `TermId`s is re-decided as the
            // clone stands: relabelling cannot reach those digits (g6_100167).
            None => {
                probe_cert_reject(|| {
                    "forged-guard arena NOT pruned: an AY-internal symbol name may \
                     spell a TermId"
                        .to_string()
                });
                true
            }
            Some(true) => true,
            Some(false) => {
                probe_cert_reject(|| {
                    "forged-guard ABSTAINED: derived-query arena rebuild could not \
                     relabel every held term"
                        .to_string()
                });
                false
            }
        }
    }
}

#[cfg(test)]
mod tests;
