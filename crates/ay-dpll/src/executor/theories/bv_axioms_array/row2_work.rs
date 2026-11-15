// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Invocation-local, generation-ordered discovery of residual read obligations.
//!
//! Existing arena entries do not change while reads are materialized. Thus a
//! persistent DFS of only appended roots discovers exactly the suffix of the
//! old whole-root DFS. Old selects cannot acquire a new array dependency. Work
//! from new selects alone therefore suffices, provided each generation keeps
//! the old ITE-before-store and store-before-select ordering.

use super::{Executor, HashSet, LateArrayReads, TermId, MAX_LATE_ARRAY_READS};

mod discovery;

use discovery::{Discovery, ReadJobs};

pub(super) fn materialize(
    executor: &mut Executor,
    extra_roots: &mut Vec<TermId>,
) -> LateArrayReads {
    materialize_with_limit(executor, extra_roots, MAX_LATE_ARRAY_READS).reads
}

struct ClosureResult {
    reads: LateArrayReads,
    #[cfg(test)]
    stats: discovery::DiscoveryStats,
}

/// The only production caller supplies the existing fixed cap. A smaller
/// private cap lets tests compare exact legacy prefixes without large arenas;
/// it does not alter the carrier's independent folded-association cap.
fn materialize_with_limit(
    executor: &mut Executor,
    extra_roots: &mut Vec<TermId>,
    root_limit: usize,
) -> ClosureResult {
    let mut closure = ReadClosure {
        known_roots: extra_roots.iter().copied().collect(),
        seen_obligations: HashSet::default(),
        reads: LateArrayReads::default(),
    };
    let mut discovery = Discovery::default();
    let mut jobs = discovery.collect(
        &executor.ctx.terms,
        executor
            .ctx
            .assertions
            .iter()
            .chain(extra_roots.iter())
            .copied(),
    );
    loop {
        // This barrier matters: reads created below are discovered only after
        // both old phases finish, not immediately when mk_select returns.
        let next_roots = extra_roots.len();
        if closure.process(executor, extra_roots, jobs, root_limit)
            || extra_roots.len() == next_roots
        {
            break;
        }
        jobs = discovery.collect(
            &executor.ctx.terms,
            extra_roots[next_roots..].iter().copied(),
        );
    }
    ClosureResult {
        reads: closure.reads,
        #[cfg(test)]
        stats: discovery.stats,
    }
}

struct ReadClosure {
    // Deliberately NOT all discovered nodes: a read already reachable through
    // an assertion still counts when it first becomes an extra root.
    known_roots: HashSet<TermId>,
    seen_obligations: HashSet<(TermId, TermId)>,
    reads: LateArrayReads,
}

impl ReadClosure {
    /// Return true only when the legacy added-root cap has been reached.
    fn process(
        &mut self,
        executor: &mut Executor,
        extra_roots: &mut Vec<TermId>,
        jobs: ReadJobs,
        root_limit: usize,
    ) -> bool {
        for (array, index) in jobs.ite.into_iter().chain(jobs.row2) {
            if !self.seen_obligations.insert((array, index)) {
                continue;
            }
            let read = self
                .reads
                .materialize_read(&mut executor.ctx.terms, array, index);
            if self.known_roots.insert(read) {
                extra_roots.push(read);
                self.reads.note_added_root();
                if self.reads.added_roots() >= root_limit {
                    return true;
                }
            }
        }
        false
    }
}

#[cfg(test)]
mod growth_tests;
#[cfg(test)]
mod tests;
