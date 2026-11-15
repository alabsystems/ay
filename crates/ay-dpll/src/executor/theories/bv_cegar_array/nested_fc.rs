// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read-path congruence for arrays of arrays in the FC audit.
//!
//! The audit in `fc_check.rs` groups reads by their DIRECT array operand, so
//! two reads of one cell of an array of arrays through different row terms,
//! `(select (select m i) j)` and `(select (select m k) l)` with `i = k` and
//! `j = l` in the SAT model, are never compared: their operands
//! `(select m i)` and `(select m k)` are different terms, and an array-valued
//! term has no bits to compare. The eager encoding instantiates that
//! congruence only for the read pairs it sees when it runs, within its
//! candidate budgets (`emit_nested_select_congruence_to_reads`), so a SAT
//! model could still give one cell two values. Model extraction then has no
//! value to publish for that cell (#8510 poisoning, `nested_reads.rs`), and
//! every round's candidate falsified an assertion over it, measured on the
//! nested QF_AUFBV fuzz families (q8002_035, q8003_136, n7001_007).
//!
//! This pass groups every scalar leaf read of an array VARIABLE by the
//! variable and the concrete value of its whole index path, and refines a
//! group whose values disagree with the FC lemma over the concatenated path:
//! `(i1 = k1 /\ .. /\ in = kn) -> (r = r')`. The lemma is `n` applications
//! of array congruence, valid in every array model, so it never removes a
//! model of the formula. It refines only, it is not part of the audit's
//! fail-closed verdict: a budget that stops it drops this round's nested
//! lemmas and leaves the bit-level verdict as it was, and nested congruence
//! is still judged by model validation (#array-select-congruence-gate), as
//! before this pass.

use std::collections::BTreeMap;

use super::*;

/// Whether an FC audit also refines read-path congruence of arrays of arrays.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum NestedReadPaths {
    /// Refine violated read paths (every audit but the last one).
    Refine,
    /// Leave them to model validation (the final residual audit, whose only
    /// question is whether the bit-level FC obligation holds).
    Skip,
}

/// Nesting depth beyond which a read path is not followed.
const MAX_PATH_DEPTH: usize = 32;

/// Leaf reads grouped by their root array variable and the concrete value of
/// their index path (the path's bits, outermost index first).
type ReadPathGroups = BTreeMap<(TermId, BigInt), Vec<FcConcreteSelect>>;

impl Executor {
    /// Append the FC lemmas for every violated read path of an array of
    /// arrays. On any budget stop the lemmas this pass added are withdrawn and
    /// the bit-level batch is left exactly as the flat audit built it.
    pub(super) fn append_nested_read_path_refinements(
        &mut self,
        select_terms: &[(TermId, TermId, TermId)],
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        already_covered: &HashSet<FcCoverKey>,
        build: &mut CegarArrayBuild,
    ) {
        let Some(groups) =
            self.nested_read_path_groups(select_terms, sat_model, lits, &mut build.inspected_bits)
        else {
            return;
        };
        let violated: Vec<&Vec<FcConcreteSelect>> = groups
            .values()
            .filter(|group| {
                group
                    .iter()
                    .skip(1)
                    .any(|entry| entry.value != group[0].value)
            })
            .collect();
        if violated.is_empty() {
            return;
        }
        let (clauses, next_var, new_vars) = (build.clauses.len(), build.next_var, build.new_vars);
        let covered = build.newly_covered.clone();
        let budget_exhausted = build.budget_exhausted;
        for group in violated {
            // The pair refinement reports a per-check budget stop by
            // setting `budget_exhausted` and skipping the pair rather
            // than failing; for this pass that is a budget stop too, so
            // withdraw everything appended here, as on a hard failure.
            if !self.append_fc_group_refinement(group, already_covered, build)
                || (build.budget_exhausted && !budget_exhausted)
            {
                build.clauses.truncate(clauses);
                build.next_var = next_var;
                build.new_vars = new_vars;
                build.newly_covered = covered;
                build.budget_exhausted = budget_exhausted;
                return;
            }
        }
    }

    /// Every scalar read at least two levels below an array variable that the
    /// assertions or the bit-blaster hold, with its whole index path encoded,
    /// grouped by root and path value. `None` on a budget stop.
    fn nested_read_path_groups(
        &mut self,
        select_terms: &[(TermId, TermId, TermId)],
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        inspected_bits: &mut usize,
    ) -> Option<ReadPathGroups> {
        let is_nested_read = |terms: &TermStore, term: TermId| {
            matches!(terms.get(term), TermData::App(sym, args)
                if sym.name() == "select"
                    && args.len() == 2
                    && matches!(terms.get(args[0]), TermData::App(inner, _) if inner.name() == "select"))
        };
        let mut leaves: Vec<TermId> = select_terms
            .iter()
            .map(|&(select, _, _)| select)
            .chain(lits.term_bits().keys().copied())
            .filter(|&term| is_nested_read(&self.ctx.terms, term))
            .collect();
        leaves.sort_unstable();
        leaves.dedup();
        if leaves.len() > budget::MAX_SELECTS {
            return None;
        }
        let mut groups = ReadPathGroups::new();
        for (position, leaf) in leaves.into_iter().enumerate() {
            if position & 0xff == 0 && self.should_abort_theory_loop() {
                return None;
            }
            let Some((root, path)) = self.nested_read_path(leaf) else {
                continue;
            };
            let Some(value_lits) = lits.scalar_lits(&self.ctx.terms, leaf) else {
                continue;
            };
            let mut index_lits = BvBits::new();
            let mut index_value = BigInt::from(0u8);
            let mut encoded = true;
            for index in path {
                let Some(bits) = lits.scalar_lits(&self.ctx.terms, index) else {
                    encoded = false;
                    break;
                };
                let value = self.concrete_value_bounded(sat_model, &bits, inspected_bits)?;
                index_value = (index_value << bits.len()) | value;
                index_lits.extend(bits);
            }
            if !encoded {
                continue;
            }
            let value = self.concrete_value_bounded(sat_model, &value_lits, inspected_bits)?;
            groups
                .entry((root, index_value.clone()))
                .or_default()
                .push(FcConcreteSelect {
                    select: leaf,
                    index_lits,
                    value_lits,
                    index_value,
                    value,
                });
        }
        Some(groups)
    }

    /// `(root, [i1, .., ik])` for a scalar read `(select .. (select root i1)
    /// .. ik)` of an array variable `root`, `k >= 2`, outermost index first.
    fn nested_read_path(&self, leaf: TermId) -> Option<(TermId, Vec<TermId>)> {
        if !matches!(
            self.ctx.terms.sort(leaf),
            Sort::BitVec(_) | Sort::Bool | Sort::FloatingPoint(_, _)
        ) {
            return None;
        }
        let mut path = Vec::new();
        let mut current = leaf;
        loop {
            match self.ctx.terms.get(current) {
                TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => {
                    if path.len() >= MAX_PATH_DEPTH {
                        return None;
                    }
                    path.push(args[1]);
                    current = args[0];
                }
                TermData::Var(_, _) => break,
                _ => return None,
            }
        }
        if path.len() < 2 {
            return None;
        }
        path.reverse();
        Some((current, path))
    }
}

#[cfg(test)]
#[path = "nested_fc_tests.rs"]
mod tests;
