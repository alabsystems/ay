// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derive the ITE-DEFINITION guard clauses that `name_non_bool_ites_all`
//! appends — by MINTING the definition the proof never carried.
//!
//! # The class, as measured
//!
//! `ay_core::TermStore::name_non_bool_ites_all` is a Tseitin-style elimination
//! of TERM-level `ite`s: every surviving non-Bool `(ite c t e)` is replaced by
//! a fresh variable `v` and the two guard assertions
//! `(or (not c) (= v t))` / `(or c (= v e))` are appended to `defs`. Those
//! assertions are not authored, so proof export demotes them to premiseless
//! `trust` steps and the mandatory strict gate refuses the whole refutation.
//!
//! Measured over all 639 `.smt2` under `benchmarks/`
//! (`AY_CENSUS=1 ay solve --no-proof -T:10`, one process per file), by an
//! INDEPENDENT re-parse of the dumped canonical S-expressions: **29 leaves in
//! one file**, `smt/chc_dt_array_model_checker_consumer_harder`, all of the shape
//!
//! ```text
//! (or (not v3) (= 1 __ay_ite_def_189))
//! (or v4       (= 0 __ay_ite_def_191))
//! ```
//!
//! The census that classified the whole `or#2` shape as "the CHC engine's own
//! array-property instantiations over `__gp*` ghost positions, a DIFFERENT
//! THEORY" is wrong about this sub-class: the `__gp*` clauses are 16 of the 94
//! `or#2` leaves, and these 29 are not array clauses at all.
//!
//! # Why the definition has to be MINTED
//!
//! `defs` is appended to the assertion stack and `check_sat` restores that
//! stack on every exit path, exactly as `purify_bool_args`' definitions are
//! (see `minted_definition_leaf`'s module docs). Measured on
//! `chc_dt_array_model_checker_consumer_harder`: `__ay_ite_def_*` occurs in **0** of the 141
//! authored assertions, in **0** `assume` steps and in **0** `fresh_def_eq`
//! steps — so there is nothing in the proof to cite. Nor is the SIBLING guard
//! clause available: the file carries one half per definiendum.
//!
//! # Where the definiens comes from, and why that is a HEURISTIC not authority
//!
//! `name_non_bool_ites_all` spells the fresh symbol
//! `__ay_ite_def_{id}` where `id` is the `TermId` of the `ite` it names. This
//! lane decodes that suffix, looks the term up, and requires it to BE an `ite`
//! of the definiendum's own sort — and then re-derives the variable from
//! `(name, sort)` and requires the SAME `TermId` back, so a forged spelling
//! that does not denote its own variable is refused.
//!
//! None of that carries authority. The soundness of a `fresh_def_eq` is the
//! conservative definitional-extension argument
//! [`ay_proof::FreshDefRegistry`] already carries and RE-DECIDES over the
//! finished proof (FRESH, INDEPENDENT, SORT, SINGLE DEFINIENS), and it does
//! not depend on the minted definiens being the one the producer chose — a
//! wrong definiens simply fails to close the derivation and the leaf keeps its
//! byte-identical `trust` step. The decode is a way of CHOOSING a candidate,
//! precisely as `minted_definition_leaf`'s alignment is.
//!
//! # What replaces the leaf
//!
//! ```text
//!  i+0  fresh_def_eq            (cl (= d I))                 :args (d)
//!  i+1  ite_branch_projection   (cl G (= I b))               a premise-free tautology
//!  i+2  eq_transitive           (cl ¬(= d I) ¬(= I b) E)     a premise-free tautology
//!  i+3  th_resolution           (cl ¬(= I b) E)
//!  i+4  th_resolution           (cl E G)
//!  i+5  or_neg                  (cl OR ¬E)
//!  i+6  th_resolution           (cl G OR)
//!  i+7  or_neg                  (cl OR ¬G)
//!  i+8  th_resolution           (cl OR OR)
//!  i+9  contraction             (cl OR)
//! ```
//!
//! `G` is the leaf's guard literal, `E` its equality literal, `OR` its own
//! or-term (byte-identical), `I` the minted definiens and `b` the branch of
//! `I` that `G`'s polarity selects. **NOTHING in the checker is touched**:
//! `fresh_def_eq`, `ite_branch_projection`, `eq_transitive`, `th_resolution`,
//! `or_neg` and `contraction` all have strict validators already, and the
//! `or_neg`/`contraction` packing is `ite_guard_promotion`'s verbatim.
//!
//! # Guards
//!
//! Each is mutation-checked in `ite_definition_leaf_tests.rs`.
//!
//! 1. **No `Anchor` steps** — their forward references the in-order remap
//!    cannot resolve.
//! 2. **A premiseless, argument-free `trust` step whose unit clause is a
//!    BINARY `or` application.**
//! 3. **One disjunct is a binary `=` whose EXACTLY ONE operand is an atomic
//!    variable named `__ay_ite_def_<id>`**; the other disjunct is the guard.
//! 4. **The decoded `id` denotes a `TermData::Ite` of the definiendum's own
//!    sort**, and that sort is not `Bool`.
//! 5. **The variable re-derives**: `mk_var(name, sort)` returns the SAME
//!    `TermId` the leaf carries.
//! 6. **The guard's polarity selects a branch that reproduces the leaf's
//!    equality literal EXACTLY** — `mk_eq(d, branch)` must be the very
//!    `TermId` the leaf's disjunct is. `mk_eq` folds Boolean equalities six
//!    ways and DISTRIBUTES over `ite`, so the built term is always decoded
//!    back rather than assumed.
//! 7. **FRESH** — the definiendum's NAME occurs in no problem assertion (both
//!    scopes) and in no `assume` of the finished proof.
//! 8. **SINGLE DEFINIENS** — one definiens per name, consistent with every
//!    `fresh_def_eq`/`fresh_def_bound` binding already in the proof and with
//!    every other definition this lane would mint in the same pass.
//! 9. **INDEPENDENT** — no minted or existing definiendum occurs inside any
//!    minted definiens.
//! 10. **The checker's OWN recognizers admit both new leaf steps** —
//!    `recognize_fresh_def_eq` for the definition and
//!    `ay_proof::recognize_ite_branch_projection` for the projection, on the
//!    exact `(clause, premises, args)` triples that will be emitted.
//! 11. **The fragment ends on the leaf's clause, byte for byte.**
//! 12. **The fragment RENDERS** under the export's own surface overrides.
//! 13. **Gate 2** — after the atomic splice, the checker's own
//!    [`ay_proof::FreshDefRegistry::collect`] is re-run over the WHOLE proof
//!    against the UNION of both authored scopes, and the entire rewrite is
//!    reverted on any decline. `commit_bridge_fragments`' backstop alone is
//!    not enough: a non-fresh definition turns a RESCUABLE `TrustStep`
//!    rejection into a HARD `InvalidTheoryLemma` one, which that backstop does
//!    not catch because the original did not certify either.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{AletheRule, Proof, ProofStep, Sort, TermData, TermId};

use super::super::Executor;

/// Largest number of `trust` leaves one call will plan for.
const MAX_ITE_DEF_LEAVES: usize = 512;

/// Largest number of nodes the definiens size check will visit. The minted
/// `ite` enters the proof's payload, and every step carrying it is metered on
/// its TREE-unfolded size, so an unbounded definiens could trade a typed
/// `TrustStep` refusal for a `ResourceLimit` one.
const MAX_DEFINIENS_NODES: usize = 256;

/// The parts of one recognized ITE-definition guard leaf.
#[derive(Clone, Copy)]
pub(super) struct IteDefinitionPlan {
    /// The leaf's own or-term, reproduced byte for byte.
    pub(super) or_term: TermId,
    /// The fresh definiendum `d`.
    pub(super) definiendum: TermId,
    /// The `ite` term `d` is defined by.
    pub(super) definiens: TermId,
    /// The leaf's guard literal `G` (`c` or `(not c)`).
    pub(super) guard: TermId,
    /// The leaf's equality literal `E` = `(= d b)` as `mk_eq` spells it.
    pub(super) equality: TermId,
    /// The branch of `definiens` that `guard`'s polarity selects.
    pub(super) branch: TermId,
}

/// Decode `__ay_ite_def_<id>` into the `TermId` its suffix names.
fn decode_definiendum_term_id(name: &str) -> Option<TermId> {
    name.strip_prefix("__ay_ite_def_")
        .and_then(|suffix| suffix.parse::<u32>().ok())
        .map(TermId)
}

/// Number of DAG nodes reachable from `term`, capped at `MAX_DEFINIENS_NODES`.
fn bounded_node_count(terms: &ay_core::TermStore, term: TermId) -> Option<usize> {
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        if seen.len() > MAX_DEFINIENS_NODES {
            return None;
        }
        match terms.get(current) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                stack.push(*condition);
                stack.push(*then_branch);
                stack.push(*else_branch);
            }
            _ => {}
        }
    }
    Some(seen.len())
}

impl Executor {
    /// Replace every premiseless `trust` leaf that is an ITE-definition guard
    /// clause with a checked derivation over a MINTED definition. Returns the
    /// number of leaves replaced.
    pub(in crate::executor) fn derive_ite_definition_guard_leaves(
        &mut self,
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) -> usize {
        // Guard 1.
        if proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Anchor { .. }))
        {
            return 0;
        }
        let leaves: Vec<(usize, TermId)> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| {
                is_ite_definition_candidate(&self.ctx.terms, step).map(|atom| (index, atom))
            })
            .take(MAX_ITE_DEF_LEAVES.saturating_add(1))
            .collect();
        if leaves.is_empty() || leaves.len() > MAX_ITE_DEF_LEAVES {
            return 0;
        }
        // Guard 7: the names no minted definiendum may carry. Computed over
        // the FINISHED proof, exactly as the checker computes FRESH.
        let constrained = self.minted_constrained_names(proof, problem_assertions);
        // Guard 8, first half: the bindings the proof already carries.
        let existing = self.existing_fresh_definitions(proof);

        let mut candidates: Vec<(usize, IteDefinitionPlan)> = Vec::new();
        for (index, atom) in leaves {
            let Some(plan) = self.plan_ite_definition(atom, &constrained, &existing) else {
                continue;
            };
            candidates.push((index, plan));
        }
        if candidates.is_empty() {
            return 0;
        }
        // Guards 8 (second half) and 9, decided over the WHOLE pass.
        if !self.ite_definitions_are_consistent_and_independent(&candidates, &existing) {
            return 0;
        }

        let overrides = self.last_proof_term_overrides.clone();
        let mut plans: Vec<Option<Vec<ProofStep>>> = vec![None; proof.steps.len()];
        let mut planned = 0usize;
        for (index, plan) in candidates {
            let Some(fragment) = self.assemble_ite_definition_fragment(&plan) else {
                continue;
            };
            // Guard 12.
            if self.bridge_fragment_is_unrenderable(&fragment, plan.or_term, overrides.as_ref()) {
                continue;
            }
            plans[index] = Some(fragment);
            planned += 1;
        }
        if planned == 0 {
            return 0;
        }
        let original = proof.steps.clone();
        let original_named = proof.named_steps.clone();
        let derived = self.commit_bridge_fragments(proof, plans);
        if derived == 0 {
            return 0;
        }
        // Guard 13 (Gate 2).
        let mut scope = self.complete_problem_assertions_for_strict_proof();
        for &assertion in problem_assertions {
            if !scope.contains(&assertion) {
                scope.push(assertion);
            }
        }
        if ay_proof::FreshDefRegistry::collect(proof, &self.ctx.terms, Some(&scope)).is_err() {
            proof.steps = original;
            proof.named_steps = original_named;
            return 0;
        }
        derived
    }

    /// Guards 8 (SINGLE DEFINIENS) and 9 (INDEPENDENT), decided over the WHOLE
    /// pass rather than one leaf at a time: two leaves may name the same
    /// definiendum (the two halves of one `ite` definition do), and a definiens
    /// minted for one leaf must not mention a definiendum minted for another.
    ///
    /// `FreshDefRegistry` re-decides both over the finished proof and Gate 2
    /// reverts the whole splice on a decline, so this is not the authority —
    /// it is what keeps a single bad candidate from costing every good one.
    fn ite_definitions_are_consistent_and_independent(
        &self,
        candidates: &[(usize, IteDefinitionPlan)],
        existing: &DetHashMap<String, TermId>,
    ) -> bool {
        let mut minted: DetHashMap<String, TermId> = DetHashMap::default();
        for (_, plan) in candidates {
            let TermData::Var(name, _) = self.ctx.terms.get(plan.definiendum) else {
                continue;
            };
            let name = name.clone();
            if minted
                .get(&name)
                .is_some_and(|&bound| bound != plan.definiens)
            {
                return false;
            }
            minted.insert(name, plan.definiens);
        }
        let mut definiendum_names: DetHashSet<String> = existing.keys().cloned().collect();
        definiendum_names.extend(minted.keys().cloned());
        let mut definiens_names: DetHashSet<String> = DetHashSet::default();
        let mut visited: DetHashSet<TermId> = DetHashSet::default();
        for &definiens in minted.values().chain(existing.values()) {
            super::minted_definition_leaf::collect_symbol_names(
                &self.ctx.terms,
                definiens,
                &mut definiens_names,
                &mut visited,
            );
        }
        !definiendum_names
            .iter()
            .any(|name| definiens_names.contains(name))
    }

    /// Guards 3-6 and 7-8 (first half) for one leaf.
    fn plan_ite_definition(
        &mut self,
        or_term: TermId,
        constrained: &DetHashSet<String>,
        existing: &DetHashMap<String, TermId>,
    ) -> Option<IteDefinitionPlan> {
        let TermData::App(symbol, disjuncts) = self.ctx.terms.get(or_term) else {
            return None;
        };
        if symbol.name() != "or" || disjuncts.len() != 2 {
            return None;
        }
        let [first, second] = [disjuncts[0], disjuncts[1]];
        if first == second {
            return None;
        }
        for (guard, equality) in [(first, second), (second, first)] {
            // Guard 3.
            let TermData::App(eq_symbol, operands) = self.ctx.terms.get(equality) else {
                continue;
            };
            if eq_symbol.name() != "=" || operands.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (operands[0], operands[1]);
            for definiendum in [lhs, rhs] {
                let TermData::Var(name, _) = self.ctx.terms.get(definiendum) else {
                    continue;
                };
                let name = name.clone();
                let Some(definiens) = decode_definiendum_term_id(&name) else {
                    continue;
                };
                // Guard 4.
                let TermData::Ite(condition, then_branch, else_branch) =
                    *self.ctx.terms.get(definiens)
                else {
                    continue;
                };
                let sort = self.ctx.terms.sort(definiens).clone();
                if sort == Sort::Bool || self.ctx.terms.sort(definiendum) != &sort {
                    continue;
                }
                if bounded_node_count(&self.ctx.terms, definiens).is_none() {
                    continue;
                }
                // Guard 5: the spelling must denote its own variable.
                if self.ctx.terms.mk_var(name.clone(), sort) != definiendum {
                    continue;
                }
                // Guard 7 / 8 (first half).
                if constrained.contains(&name) {
                    continue;
                }
                if existing.get(&name).is_some_and(|&bound| bound != definiens) {
                    continue;
                }
                // Guard 6: the guard's polarity picks the branch, decoded the
                // way `validate_ite_branch_projection` decodes it (a literal
                // `Not` node over the ite's OWN condition, or the condition
                // itself), and the rebuilt equality must be the leaf's own
                // literal.
                let branch = match self.ctx.terms.get(guard) {
                    TermData::Not(inner) if *inner == condition => then_branch,
                    _ if guard == condition => else_branch,
                    _ => continue,
                };
                if self.ctx.terms.mk_eq(definiendum, branch) != equality {
                    continue;
                }
                return Some(IteDefinitionPlan {
                    or_term,
                    definiendum,
                    definiens,
                    guard,
                    equality,
                    branch,
                });
            }
        }
        None
    }
}

/// Whether `step` is a leaf this lane may replace (Guard 2).
fn is_ite_definition_candidate(terms: &ay_core::TermStore, step: &ProofStep) -> Option<TermId> {
    let ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises,
        args,
    } = step
    else {
        return None;
    };
    if !premises.is_empty() || !args.is_empty() || clause.len() != 1 {
        return None;
    }
    let atom = clause[0];
    match terms.get(atom) {
        TermData::App(symbol, disjuncts) if symbol.name() == "or" && disjuncts.len() == 2 => {
            Some(atom)
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "ite_definition_leaf_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "ite_definition_leaf_guard_tests.rs"]
mod guard_tests;

#[cfg(test)]
#[path = "ite_definition_leaf_negative_tests.rs"]
mod negative_tests;
