// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Witness sources for the negated-existential ground-instantiation lane
//! beyond the authored ground scan (#negated-exists-cegqi-witness-hints).
//!
//! THE GAP THIS CLOSES. On the deductive-checks `exists`-typed obligation shape
//!
//! ```smt2
//! (assert (not (exists ((i Int)) (and (<= 0 i) (< i 4294967296) (< 300 i)))))
//! ```
//!
//! NNF turns the root into a fresh universal, CEGQI finds the witness `301`
//! (Reynolds, King, Kuncak, FMSD 2017 — the selection term or the model
//! value), the ground instance refutes the query, and mandatory authored-scope
//! certification then declines: the only witness source of the lane in
//! `authored_negated_exists_ground_inst` is the authored ground scan, which
//! deliberately never descends under a binder, and outside the existential
//! body the problem has no `Int` term at all. The engine had the witness in
//! hand and the certificate could not name it.
//!
//! The sibling shape, `seq_contains` on both sides,
//!
//! ```smt2
//! (assert (exists ((i Int)) (and (<= 0 i) (< i n) (= #x05 (select s ((_ int2bv 64) i))))))
//! (assert (not (exists ((j Int)) (and (<= 0 j) (< j n) (= #x05 (select s ((_ int2bv 64) j)))))))
//! ```
//!
//! needs the Skolem constant the deep Skolemizer minted for the POSITIVE
//! existential: `B[sk]` is a recorded, `sko_ex`-derivable consequence of the
//! authored `(exists ...)` (`SkolemInstanceRecord`, positive), and
//! `(not B)[sk]` is a `forall_inst` consequence of the dual, so the pair is a
//! ground contradiction — but `sk` is not an authored subterm either.
//!
//! TWO ADDITIVE SOURCES, SAME LANE, NO KNOB. Both are consulted only inside
//! `plan_negated_exists_ground_instances`, and only after the consulting
//! firewall legs declined, so the reachable transition stays `unknown ->
//! unsat`:
//!
//! 1. the fresh Skolem constants of positive single-binder authored
//!    existentials (`skolem_instance_records`, `positive`), FIRST — the
//!    consequence-replay stitcher already derives `B[sk]` through the strict
//!    `Skolem` (`sko_ex` reading) step whose validator authenticates binder,
//!    sort and UNNEGATED body against the live choice registry;
//! 2. the closed binder values the CEGQI rounds instantiated with during this
//!    check-sat (`cegqi_witness_hints`, recorded at the
//!    `append_cegqi_ground_instance` chokepoint after its own sort and
//!    exact-substitution checks).
//!
//! Every candidate is re-filtered here for PROBLEM-CLOSEDNESS: it mentions no
//! binder name bound anywhere in the authored scope, contains no binder of its
//! own, and every free symbol in it is either an authored symbol or a
//! registered Skolem symbol — so a CEGQI counterexample constant can never
//! reach a certificate. Nothing is taken on trust past that: `forall_inst`
//! holds for ANY closed term (`∀x⃗.¬φ ⊨ ¬φ[t⃗]`), and the strict validator
//! re-derives arity, sorts, groundness and the exact simultaneous
//! substitution, so a wrong hint is a declined candidate, never a wrong step.
//! Hints come BEFORE the authored scan so the per-sort cap can never evict the
//! value that actually refuted the query.

use super::*;

/// Node budget for the authored-symbol and closedness scans.
const MAX_HINT_SCAN_WORK: usize = 20_000;

impl Executor {
    /// Ground witness candidates of `sort` for one binder of an authored
    /// negated existential, hints first, then the authored ground scan;
    /// deduplicated and capped at `limit`.
    pub(super) fn negated_exists_witness_candidates(
        &self,
        authored: &[TermId],
        sort: &Sort,
        bound_names: &ay_core::kani_compat::DetHashSet<String>,
        extra_skolem: &[crate::executor::SkolemInstanceRecord],
        limit: usize,
    ) -> Vec<TermId> {
        let symbols = self.authored_symbol_nodes(authored);
        let mut out: Vec<TermId> = Vec::new();
        let admit = |candidate: TermId, out: &mut Vec<TermId>| {
            if out.len() < limit
                && !out.contains(&candidate)
                && self.ctx.terms.sort(candidate) == sort
                && self.term_avoids_names(candidate, bound_names)
                && self.term_is_problem_closed(candidate, &symbols)
            {
                out.push(candidate);
            }
        };
        for record in self.skolem_instance_records.iter().chain(extra_skolem) {
            if record.positive {
                admit(record.witness, &mut out);
            }
        }
        for (hint_sort, hint) in &self.cegqi_witness_hints {
            // The ledger outlives internal re-solves; a term-store rollback in
            // between would leave an id past the arena, which must not be
            // dereferenced. An in-range stale id can only name some other
            // term, which the filters below and the strict validator judge.
            if hint_sort == sort && hint.index() < self.ctx.terms.len() {
                admit(*hint, &mut out);
            }
        }
        for candidate in self.ground_witnesses_for_sort(authored, sort, bound_names) {
            admit(candidate, &mut out);
        }
        out
    }

    /// The hinted values of `sort` in `ledger` (`cegqi_witness_hints` or
    /// `instance_witness_hints`) whose every free symbol is AUTHORED,
    /// deduplicated and capped at `limit`. Stricter than
    /// [`Self::negated_exists_witness_candidates`], which also admits Skolem
    /// symbols: the implied-universal lane, its only consumer, has no
    /// derivation that could introduce one into a certificate
    /// (#iff-split-implied-authority).
    pub(super) fn authored_witness_hint_terms(
        &self,
        ledger: &[(Sort, TermId)],
        authored: &[TermId],
        sort: &Sort,
        bound_names: &ay_core::kani_compat::DetHashSet<String>,
        limit: usize,
    ) -> Vec<TermId> {
        let symbols = self.authored_symbol_nodes(authored);
        let mut out: Vec<TermId> = Vec::new();
        for (hint_sort, hint) in ledger {
            if out.len() >= limit {
                break;
            }
            // Same arena guard as above: a stale id past the arena is skipped.
            if hint_sort == sort
                && hint.index() < self.ctx.terms.len()
                && !out.contains(hint)
                && self.term_avoids_names(*hint, bound_names)
                && self.term_is_closed_over(*hint, &symbols, false)
            {
                out.push(*hint);
            }
        }
        out
    }

    /// Positive-existential Skolem provenance REBUILT from the persistent
    /// choice registry for the exact authored `(exists ((x S)) B)` roots.
    ///
    /// `skolem_instance_records` is per internal solve: the CEGAR refinement
    /// loop re-prepares the executor between iterations, and the Skolemized
    /// assertion is replaced in place, so a later iteration (where the
    /// artifact firewall runs) holds no record for a witness minted earlier.
    /// The `TermStore` choice registry is the durable source: a witness whose
    /// registered `SkolemChoice` names this root's binder, sort and UNNEGATED
    /// body is `εx.B`, and `B[x := sk]` follows from the root by the choice
    /// axiom (Alethe `sko_ex`). The record is a hint only — the strict
    /// `Skolem` validator re-authenticates all four against the registry.
    pub(super) fn authored_positive_exists_skolem_records(
        &mut self,
        authored: &[TermId],
    ) -> Vec<crate::executor::SkolemInstanceRecord> {
        /// Registry-rebuilt records admitted per public query.
        const MAX_REBUILT_SKOLEM_RECORDS: usize = 8;
        let choices: Vec<(TermId, ay_core::SkolemChoice)> = self
            .ctx
            .terms
            .skolem_choices()
            .map(|(witness, choice)| (witness, choice.clone()))
            .collect();
        let mut records = Vec::new();
        for &root in authored {
            let TermData::Exists(bindings, body, _) = self.ctx.terms.get(root).clone() else {
                continue;
            };
            let [(binder, sort)] = bindings.as_slice() else {
                continue;
            };
            for (witness, choice) in &choices {
                if records.len() >= MAX_REBUILT_SKOLEM_RECORDS {
                    return records;
                }
                if choice.binder != *binder
                    || choice.sort != *sort
                    || choice.body != body
                    || self
                        .skolem_instance_records
                        .iter()
                        .any(|record| record.witness == *witness)
                {
                    continue;
                }
                let Some(instance) = Self::substitute_single_binder_structurally(
                    &mut self.ctx.terms,
                    body,
                    binder,
                    *witness,
                ) else {
                    continue;
                };
                records.push(crate::executor::SkolemInstanceRecord {
                    source: root,
                    quantified: root,
                    witness: *witness,
                    instance,
                    asserted: instance,
                    positive: true,
                });
            }
        }
        records
    }

    /// Every `Var` node reachable from the authored roots, binders' bodies
    /// included. Bounded: an exhausted scan yields a SMALLER set, which can
    /// only make the closedness filter below reject more.
    fn authored_symbol_nodes(
        &self,
        authored: &[TermId],
    ) -> ay_core::kani_compat::DetHashSet<TermId> {
        let mut symbols = ay_core::kani_compat::DetHashSet::default();
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut stack = authored.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) || seen.len() > MAX_HINT_SCAN_WORK {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::Var(..) => {
                    symbols.insert(term);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                _ => {}
            }
        }
        symbols
    }

    /// Whether every free symbol of `term` is an authored symbol or a
    /// registered Skolem symbol. Conservative: an exhausted scan, a binder or a
    /// `let` answers `false`.
    fn term_is_problem_closed(
        &self,
        term: TermId,
        symbols: &ay_core::kani_compat::DetHashSet<TermId>,
    ) -> bool {
        self.term_is_closed_over(term, symbols, true)
    }

    /// [`Self::term_is_problem_closed`], with registered Skolem symbols
    /// admitted only when `admit_skolems`.
    fn term_is_closed_over(
        &self,
        term: TermId,
        symbols: &ay_core::kani_compat::DetHashSet<TermId>,
        admit_skolems: bool,
    ) -> bool {
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut stack = vec![term];
        while let Some(node) = stack.pop() {
            if !seen.insert(node) {
                continue;
            }
            if seen.len() > MAX_HINT_SCAN_WORK {
                return false;
            }
            match self.ctx.terms.get(node) {
                TermData::Var(name, _) => {
                    if !symbols.contains(&node)
                        && !(admit_skolems && self.ctx.terms.is_skolem_symbol(name))
                    {
                        return false;
                    }
                }
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return false,
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                _ => {}
            }
        }
        true
    }
}
